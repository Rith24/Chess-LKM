#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/fs.h>
#include <linux/miscdevice.h>
#include <linux/device.h>
#include <linux/uaccess.h>
#include <linux/types.h>
#include <linux/string.h>
#include <linux/slab.h>
#include <linux/rwsem.h>




MODULE_LICENSE("GPL");


//reader writer semaphore for synchronizing tictactoe resource access
static DECLARE_RWSEM(board_lock);
static DECLARE_RWSEM(resp_lock);

//response strings
static char *OK = "OK\n";
static char *UNKCMD = "UNKCMD\n";
static char *INVFMT = "INVFMT\n";
static char *CHECK = "CHECK\n";
static char *MATE = "MATE\n";
static char *ILLMOVE = "ILLMOVE\n";
static char *OOT = "OOT\n";
static char *NOGAME = "NOGAME\n";
static char *TIE = "TIE\n";

//response buffer
static char *response = "NOGAME\n";
static size_t resplen = 7;

//cmd string array
//static char *commands[5] = {"00", "01", "02", "03", "04"}; 


//board in string format and game elements
static char boardstr[129];
static bool game_initialized = false;
static bool mated = false;
static char turn = '\0';
static char human = '\0';
static char comp = '\0';

static int games = 0;

//2d array of char chess piece pointers 
static char *board[8][8];

/*this piece stores dynamically allocated pointers to promoted pawn strings.
  necesary because when promoting, the statically declared strings can't be 
  changed, and promoting a pawn requires this change. The pointers in this array
  will all be freed in reset(). 
  
  Note that array size is 16 because only 16 promotions
  are possible in the game (8 promotions for 8 pawns for each player)*/
static char *promoted_pieces[16] = {NULL};

/*this index keeps track of the next empty
 index in promoted_pieces[]*/
static int index = 0;

//chess pieces
static char *EMPTY = "**";
static char WHITE = 'W';
static char BLACK = 'B';
static char KING = 'K';
static char QUEEN = 'Q';
static char BISHOP = 'B';
static char KNIGHT = 'N';
static char ROOK = 'R';
static char PAWN = 'P';


//this is the arrangement of pieces in row order
//used by reset() to memcpy into the enum 2d array and reset
static char *whites[2][8] ={{"WR", "WN", "WB", "WQ", "WK", "WB", "WN", "WR"}, {"WP", "WP", "WP", "WP", "WP", "WP", "WP", "WP"}};
static char *blacks[2][8] ={{"BR", "BN", "BB", "BQ", "BK", "BB", "BN", "BR"}, {"BP", "BP", "BP", "BP", "BP", "BP", "BP", "BP"}}; 

//row of empty squares
static char *empty[8] = {"**", "**", "**", "**", "**", "**", "**", "**"};

//x and y coordinates of the black and white kings' positions
static int bkingpos[2] = {7, 4};
static int wkingpos[2] = {0, 4};


//number of moves made in the game
static int moves = 0;



//validates the piece for correct color char and piece char
static bool validPiece(char color, char piece)
{
    if (color == WHITE || color == BLACK){
        if (piece == KING || piece == QUEEN || piece == KNIGHT || piece == BISHOP || piece == ROOK || piece == PAWN){
            return true;
        }
    }

    return false; 
}



//validates the square to square coordinates  
static bool validIndex(char rowa, char rowb, char cola, char colb){
    bool valid = true;

    if (rowa < 'a' || rowb < 'a' || rowa > 'h' || rowb > 'h'){
        valid = false;
    }

    if (cola < '1' || colb < '1' || cola > '8' || colb > '8'){
        valid = false;
    }

    return valid; 

}


/*checks if a multi-square straight path a piece is moving on is unblocked
  needs to be called only for rook, bishop, and queen*/

static bool blocked(int i0, int i1, int j0, int j1)
{
    //these are the increment variables, either 1 or -1
    int di = 0, dj = 0;
    //these are the x and y axis distances
    int ilim = i1 - i0;
    int jlim = j1 - j0;

    int i = 0, j = 0;


    /*it its a vertical path j increment = 1 and i increment = 0
     and vice versa for horizontal path*/ 
    if (i0 == i1){
        dj = 1;
    }

    else if (j0 == j1){
        di = 1;
    }

    /* if its a diagonal path, then di and dj = +/- 1 */

    else{
        if (ilim > 0){
            di = 1;
        } 

        else{
            di = -1;
        }

        if (jlim > 0){
            dj = 1;
        }

        else{
            dj = -1;
        }
    }

    /*this ensures that ilim and jlim is positive (for the while loop below)
     and yields the absolute value x and y axis travel distances*/
    ilim = (i1 > i0) ? (i1 - i0) : (i0 - i1);
    jlim = (j1 > j0) ? (j1 - j0) : (j0 - j1);


    /*keeps going as long as there's an x or y axis
      distance to cover. ilim = jlim for diagonal paths
      
      NOTE: the bound is ilim - 2 and jlim - 2 because we 
      do not want to check the starting and ending positions.
      we just want to see what pieces are STRICTLY inbetween 
      blocking the path*/
    while (i < ilim - 2 || j < jlim - 2){

        char *piece = board[i0 + di][j0 + dj];

        /*if any one square is non empty, then path is blocked*/
        if (strcmp(piece, EMPTY)){
            return true;
        }

        /*go to the next square*/

        i0 += di;
        j0 += dj;
        i++;
        j++;

    }

    /*otherwise path is clear*/
    return false;

}



static bool validate(char *cmd, size_t len)
{
    /*these exist for locking purposes to check if 
      changing the response string is necessary (since its a shared variable as well)
    */
    char *resp = NULL;
    bool error = false;

    //validate the first two characters that make up the command
    if (cmd[0] != '0'){
        resp = UNKCMD;
        error = true;
    }

    if (cmd[1] != '0' && cmd[1] != '1' && cmd[1] != '2' && cmd[1] != '3' && cmd[1] != '4'){
        resp = UNKCMD;
        error = true;
    }

    //make sure last char is the newline char
    if (cmd[len - 1] != '\n'){
        resp = INVFMT;
        error = true;
    }

    //now validate the args
    if (cmd[1] == '0'){

        /*string length sould be fine and third char
          should be a space*/ 
        if (len != 5 || cmd[2] != ' '){
            resp = INVFMT;
            error = true;
        }

        //make sure right piece color choice char is included 
        if ((cmd[3] != WHITE && cmd[3] != BLACK) || cmd[4] != '\n'){
            resp = INVFMT;
            error = true;
        }
    }


    else if (cmd[1] == '2'){

        //check if its one of the possible move command string lengths (11, 14, 17) 
        //and check for hyphen, space and newline formatting
        if ((len != 11 && len != 14 && len != 17) || cmd[2] != ' ' || cmd[7] != '-' || cmd[len - 1] != '\n'){
            resp = INVFMT;
            error = true;
        }

        //check string format up to the starting to ending move position part

        
        if (!(validPiece(cmd[3], cmd[4])) || !(validIndex(cmd[5], cmd[8], cmd[6], cmd[9]))){
            resp = INVFMT;
            error = true; 
        }

        //validating a capture, promotion, or capture/promotion string
        if (len >= 14){
            //check for a capture or promotion char
            if ((cmd[10] != 'x' && cmd[10] != 'y') || !(validPiece(cmd[11], cmd[12]))){
                resp = INVFMT;
                error = true;
            }

            //for a capture/promotion string, 'x' comes first, 'y' second
            if (len == 17){
                if (cmd[10] != 'x' || cmd[13] != 'y' || !(validPiece(cmd[14], cmd[15]))){
                    resp = INVFMT;
                    error = true;
                }
            }
        }
    }  
 

    /*if the string is valid, the board_lock will never be taken
      and in the long run, increases concurrency
    */  
    if (error){
        down_write(&resp_lock);
        response = resp;
        resplen = 7;
        up_write(&resp_lock);

        return false;
    
    }

    return true;

}



static void reset(char piece)
{
    
    int i;

    //delete all the promoted pieces stored and set to null
    for (i = 0; i < 16; i++){
        if (promoted_pieces[i] != NULL){
            kfree(promoted_pieces[i]);
            promoted_pieces[i] = NULL;
        }
    }

    index = 0;

    //this resets the white and black sides to original formation
    memcpy(board[0], whites[0], 8 * sizeof(char *));
    memcpy(board[1], whites[1], 8 * sizeof(char *));
    memcpy(board[7], blacks[0], 8 * sizeof(char *));
    memcpy(board[6], blacks[1], 8 * sizeof(char *));


    //this loop fills out the blank spaces in the board
    for (i = 2; i < 6; i++){
        memcpy(board[i], empty, 8 * sizeof(char *));
    }

    //reset game variables
    games++;
    game_initialized = true;
    mated = false;
    moves = 0;

    wkingpos[0] = 0;
    wkingpos[1] = 4;
    bkingpos[0] = 7;
    bkingpos[1] = 4;
    
    human = piece;

    // set turn 
    if (piece == WHITE){
        comp = BLACK;
        turn = human;
    }


    else{
        comp = WHITE;
        turn = comp;
    }

}

static bool check(int i, int j, char player)
{
    /*the idea is to start from the king's square
      and work our way outwards linearly along all
      8 directions to see if there is a check by an 
      opponent's piece*/

    //this is the increment variable for spanning to outward squares
    int inc = 1;

    /* arrays of x and y coordinate travel paths
       varies by incrementing inc. each combination of elements
       in iindexes and jiindexes represents one of 8 possible directions spanning 
       outward from square (i, j).*/ 
    int iindexes[3] = {i + inc, i - inc, i};
    int jindexes[3] = {j + inc, j - inc, j};

    
    int k = 0, l = 0, m = 0, n = 0;

    /*this array keeps track of whether or not each of the
      8 different directions should be checked*/
    int dir[3][3] = {0};    
    
    /*this is searching for any horses that may be 
      putting the king in check */

    /* x and y travel displacement values;
       each combination of dx and dy elements 
       represents one of a horse's 8 possible 
       L shaped paths */ 

    int dx[2] = {1 , -1};
    int dy[2] = {2, -2};

    char *piece1 = NULL;
    char *piece2 = NULL;

    char color1 = 0, type1 = 0, color2 = 0, type2 = 0;

    char opponent;

    if (player == WHITE){
        opponent = BLACK;
    }

    else{
        opponent = WHITE;
    }
    

    down_read(&board_lock);

    /*iterating through possible horse paths*/

    for (k = 0; k < 2; k++){
        m = dx[k];
        
        for (l = 0; l < 2; l++){
            n = dy[l];
            

            /*check if indices are valid*/

            if (i + m < 7 && i + m > 0 && j + n < 7 && j + n > 0){
                piece1 = board[i + m][j + n];
                color1 = piece1[0];
                type1 = piece1[1];
            }

            
            if (i + n < 7 && i + n > 0 && j + m < 7 && j + m > 0){
                piece2 = board[i + n][j + m];
                color2 = piece2[0];
                type2 = piece2[1];
            }
            
            /* check if the piece is an opponent's horse
               return check if yes */
            if ((color1 != player && type1 == KNIGHT) || (color2 != player && type2 == KNIGHT)){
                goto yes;
            } 
            
        }
        
    }
    
   

    /*its while inc < 8 because max dimension span length 
      for length, width, or diagonals is only 8 squares*/ 
    while (inc < 8){
        
        for (k = 0; k < 3; k++){
            
            m = iindexes[k];
    
            //makes sure that we dont exceed the board dimensions
            if (m > 7 || m < 0){
                continue;
            }

            for (l = 0; l < 3; l++){ 

                n = jindexes[l];

                /*
                printk("m is: %d\n", m);
                printk("n is: %d\n", n);
                */

                /* if this direction should not be checked,
                   or if its the origin king square, then 
                   pass this iteration*/
    
                if (dir[k][l] == 1 || (m == i && n == j)){
                    continue;
                }
                
                if (n > 7 || n < 0){
                    continue;
                }

                //we don't need to check square (i, j); its the king's square    
                if (m == i && n == j){
                    continue;
                }

                else{
                    char *piece = board[m][n];
                    char color = piece[0];
                    char type = piece[1];

                    /*path is blocked by your piece so no need
                      to ever check this direction again*/

                    if (color == player){
                        dir[k][l] = 1;
                        continue;
                    }

                    /*if its opponent piece, check piece types with
                      respect to the direction*/ 

                    else {
                        //this is for vertical-horizontal directions
                        
                        if (inc == 1 && type == KING){
                            goto yes;
                        }
                        
                        else if (type == QUEEN){
                            goto yes;
                        }

                        else if ((m == i || n == j)){
                            if (type == ROOK){
                                goto yes;
                            }
                        }
                        
                
                        //this is for diagonal directions

                        else if (type == BISHOP){
                            goto yes;
                        }

                        else if (inc == 1 && type == PAWN){

                            /* check if the pawns are checking the king from
                               the correct side. the pawn might be behind the king
                               on the other side of the board and not pose a threat*/

                            if (player == WHITE && m > i ){
                                goto yes;
                            }

                            else if (player == BLACK && m < i){
                                goto yes;
                            } 
                        } 
                        
                        /* if the piece is non-threatening and not empty,
                           then there is no more need to keep
                           checking this direction. But the "piece
                           could be a blank char, so this check
                           is necessary*/
                        if (color == opponent){   
                            dir[k][l] = 1;
                        }

                    }
                }
            }
        }
        
        inc++;

        /*ISO C90 forbids redeclaring the iindexes 
          and jindexes array at top of while loop, so
          the array elements have to be reset manually*/ 
        iindexes[0] = i + inc;
        iindexes[1] = i - inc;
        iindexes[2] = i;
        jindexes[0] = j + inc;
        jindexes[1] = j - inc;    
        jindexes[2] = j;

    }   

    up_read(&board_lock);

    return false;

yes:
    up_read(&board_lock);
    return true;

}





/*checks if a king is mated*/

static bool mate(int i, int j, char player)
{  

    int k, l;
    int m, n;

    char* king = NULL;

    //up_read(&board_lock);
    down_write(&board_lock);

    /*store the king position coordinates*/

    if (player == WHITE){
        i = wkingpos[0];
        j = wkingpos[1];
    
    }

    else{
        i = bkingpos[0];
        j = bkingpos[1];

    }

    /*this is necessary because when we are checking the safety of the 
      king's surrounding squares, we dont want to mistake the king piece
      that's still in the original position as a blocking piece that protects the king.*/
    king = board[i][j];
    board[i][j] = EMPTY;

    up_write(&board_lock);

    /*braces added to allow declaration of the two below arrays since we
      can't declare array at the very top of the function and then
      initialize it as a whole array*/  
    {
        /*these two arrays are the possible x and y values of the squares
        surrounding the king's current position*/ 
        int iindexes[3] = {i + 1, i - 1, i};
        int jindexes[3] = {j + 1, j - 1, j};


        /*same kind of iteration method as check()
          except we are only looking at squares adjacent
          to the king's square and seeing if there exists a 
          square that the king can legally move to */

        for (k = 0; k < 3; k++){
            m = iindexes[k];

            //makes sure that we dont exceed the board dimensions
            if (m > 7 || m < 0){
                continue;
            }

            for (l = 0; l < 3; l++){
                n = jindexes[l];

                //makes sure that we dont exceed the board dimensions
                if (n > 7 || n < 0){
                    continue;
                }

                if (m == i && n == j){
                    continue;
                }

                else{
                    char *piece = board[m][n];
                    char color = piece[0];

                    /*if not in check and square is either empty or its an opponent's piece
                      then king is not mated
                      */
                    if ((!check(m, n, player)) && (!strcmp(piece, EMPTY) || color != player)){

                        //set the king back in its place
                        down_write(&board_lock);
                        board[i][j] = king;
                        up_write(&board_lock);

                        return false;

                    }
                }
            }
        }
    }
    
    
    down_write(&board_lock);

    //set the king back in its place
    board[i][j] = king;
    mated = true;
    game_initialized = false;
    
    up_write(&board_lock);
    
    return true;

}


static bool check_or_mate(int i, int j, char player)
{
    /*calling mate() after calling check() in a nested 
      if statement because check needs to be true for 
      mate to be true*/

    if (check(i, j, player)){
        down_write(&resp_lock);
    
        response = CHECK;
        resplen = 6;

       
        if (mate(i, j, player)){
        
            response = MATE;
            resplen = 5;
            up_write(&resp_lock);

            return true;
        
        }
        
        up_write(&resp_lock);

        return true;

    }

    return false;

}





/*computer only moves the king. The computer
  will always make a legal move by moving only
  the king until the king is mated or a stalemate 
  occurs*/  

static void computer_move(void)
{
    //char *src = NULL;
    char *resp = NULL;
    size_t len = 0;

    char *king = NULL;
    bool white = false, black = false, computer = false;
    
    int i, j, k, l, m, n;

    down_read(&board_lock);

    if (turn == comp){
        computer = true;
    }

    if (comp == WHITE){
        white = true;
        i = wkingpos[0];
        j = wkingpos[1];
    }

    else{
        black = true;
        i = bkingpos[0];
        j = bkingpos[1];
    }

    up_read(&board_lock);

    
    if (computer){
        down_write(&board_lock);

        /*moves a center pawn if its black or white's
          first move*/

        if (moves <= 1){
            if (white){
                char *pawn = board[1][4];
                board[3][4] = pawn;
                board[1][4] = EMPTY;

                moves++;
                turn = human;
                resp = OK;
                len = 3;

                up_write(&board_lock);
                goto ret;

            }

            else{
                char *pawn = board[6][4];
                board[4][4] = pawn;
                board[6][4] = EMPTY;

                moves++;
                turn = human;
                resp = OK;
                len = 3;
                
                up_write(&board_lock);
                goto ret;
            }

        }

        /*after first move, move the king*/

        else{
            king = board[i][j];
            board[i][j] = EMPTY;

            up_write(&board_lock);

            {
                /*this is the same iterative method as mate()
                  modified to move the king if there is a non checked
                  legal square */

                int iindexes[3] = {i + 1, i - 1, i};
                int jindexes[3] = {j + 1, j - 1, j};

                for (k = 0; k < 3; k++){
                    m = iindexes[k];

                    //makes sure that we dont exceed the board dimensions
                    if (m > 7 || m < 0){
                        continue;
                    }

                    for (l = 0; l < 3; l++){
                        n = jindexes[l];

                        //makes sure that we dont exceed the board dimensions
                        if (n > 7 || n < 0){
                            continue;
                        }

                        if (m == i && n == j){
                            continue;
                        }

                        else{
                            char *piece = board[m][n];
                            char color = piece[0];
                            
                            /*if not in check and square is either empty or its an opponent's piece*/
                            if (!check(m, n, comp)){

                                if((!strcmp(piece, EMPTY)) || color != comp){
            
                                    down_write(&board_lock);

                                    /*set the king back in its place*/
                                    board[m][n] = king;
                                    board[i][j] = EMPTY;

                                    /*update king position*/
                                    if (white){
                                        wkingpos[0] = m;
                                        wkingpos[1] = n;
                                    }

                                    else{
                                        bkingpos[0] = m;
                                        bkingpos[1] = n;
                                    }

                                    turn = human;
                                    resp = OK;
                                    len = 3;
                                    moves++;

                                    up_write(&board_lock);
                                    goto ret;

                                }
                            }
                        }     
                    }
                }
            }
        }


        /* if program flow reaches this code,
           then that means computer couldn't make a
           move (stalemate) */

        down_write(&board_lock);

        board[i][j] = king;
        turn = human;
        game_initialized = false;

        up_write(&board_lock);

        resp = TIE;
        len = 4;

    }

    else{
        resp = OOT;
        len = 4;
    }


ret:

    down_write(&resp_lock);
    response = resp;
    resplen = len;
    up_write(&resp_lock);

}





static void print(void)
{
    int i, j;
    char *itr = boardstr;

    /*iterate the board and copy each piece 
      into boardstr*/
      
    for (i = 0; i < 8; i++){
        for (j = 0; j < 8; j++){

            char *piece = board[i][j];
            memcpy(itr, piece, 2);

            itr += 2;

        }
    }

    boardstr[128] = '\n';    

}



/*checks if a move made by the user is legal*/

static bool validateMove(char *cmd, size_t len)
{   
    
    int i0 = 0, j0 = 0, i1 = 0, j1 = 0, i = 0, j = 0;

    char *src = NULL;
    char *dest = NULL;

    char color = cmd[3];
    char type = cmd[4];

    char promoted_type = '\0';

    /*these are the source and destination pieces listed by the cmd string
     they've been initialized to two chars statically rather than dynamically 
     allocating memory to make things simpler */

    char spiece[] = "**";
    char dpiece[] = "**";

    bool captured = false;
    bool promoted = false;

    //not human's piece
    if (color != human){
        goto err;
    }
    
    /*Note: j and i assignments are flipped bc 2d array is stores as an array of row arrays
      EX: b3 -> (1, 2) in the chess board. but board[1][2] actually yields (2, 1) square 
      in the actual board (because 2d array is stored as arrays of rows)
      
      so basically setting j equal to the letter index and i to the number index 
      transforms the 2d array orientation into the chess board x-y axis notation*/

    i0 = cmd[5] - 'a';
    j0 = cmd[6] - '1';

    src = board[j0][i0];

    i1 = cmd[8] - 'a';
    j1 = cmd[9] - '1';

    dest = board[j1][i1];

    spiece[0] = cmd[3];
    spiece[1] = cmd[4];
    

    /*check if the piece to be moved is actually in the specified square*/
    
    if (src[0] != spiece[0] || src[1] != spiece[1]){
        goto err;
    }
    
    /*
    if (strcmp(spiece, src)){
        printk("2\n");
        goto err;
    }
    */

    /*if its a simple move and destination square isn't empty*/
    if (len == 11 && dest[0] != '*'){
        goto err;
    }


    if (len >= 14){
                
        //opponent piece is captured 
        //this may or may not happen for a string len of 14
        //this check definitiely happens for a string length of 17 (capture and pawn promotion)
        if (cmd[10] == 'x'){
            
            dpiece[0] = cmd[11];
            dpiece[1] = cmd[12];

            if (strcmp(dpiece, dest)){
                goto err;
            }

            captured  = true;

        }

        /* or piece is being promoted only, then check if its a pawn
          this ctrl statement is only accesed by a 14 char string*/
        
        else {
            if (type != PAWN || dest[0] != '*' || cmd[11] != human){
                goto err;
            }

            promoted = true;
            promoted_type = cmd[12];

        }


        /*this is same as previous else if check basically
         specifically for 17 length string. capture check 
         is already done in the first "if" statement*/

        if (len == 17){
            if (type != PAWN || cmd[14] != human){
                goto err;
            }

            promoted = true;
            promoted_type = cmd[15];

        }
    } 

    /*now we check if the actual piece movement is valid and move if valid
      for details regarding the arithmetic rules for each type of piece, 
      please check the design document*/

    if (type == PAWN){
        
        /*if a piece is captured then check if the pawn moves one space forward diagonally*/
        if (captured){
            //j1 - j0 is positive (forward) for white
            if (color == WHITE && ((j1 - j0 != 1) || (i1 - i0 != 1 && i1 - i0 != -1))){ 
                goto err;
            }

            //j0-j1 is positive (forward) for black
            else if (color == BLACK && ((j0 - j1 != 1) || (i1 - i0 != 1 && i1 - i0 != -1))){
                goto err;
            } 
 
        }

        //check if the pawn has reached the other side if promoted
        if (promoted){
            if (color == WHITE && j1 != 7){
                goto err;
            }

            else if (color == BLACK && j1 != 0){
                goto err;
            }

        }

        /*check for normal move, 1 step forward, pawn is neither promoted 
          or captured*/

        if (!promoted && !captured){
            if (color == WHITE && (i1 != i0 || (j0 == 1 && j1 - j0 != 2 && j1 - j0 != 1) || (j0 != 1 && j1 - j0 != 1))){
                goto err;
            }

            //black pawn travels one index down the y axis
            else if (color == BLACK && (i1 != i0 || (j0 == 6 && j0 - j1 != 2 && j0 - j1 != 1) || (j0 != 6 && j0 - j1 != 1))){
                goto err;
            }

        }

        goto mov;

    }


    if (type == ROOK){
         
        //constraint for vertical/horizontal rook movement  
        if (i0 != i1 && j0 != j1){
            goto err;
        }
    
        if (!blocked(j0, j1, i0, i1)){
            goto mov;
        }

        else{
            goto err;
        }

    }

    if (type == KNIGHT){
        int product = (i1 - i0) * (j1 - j0);

        if (product != 2 && product != -2){
            goto err;
        }

        goto mov;

    }

    if (type == BISHOP){
        int slope = 0;
        
        /*this just makes sure that we don't divide by zero
          since its behavior is undefined*/
        if (j0 == j1){
            goto err;
        }

        slope = (i1 - i0) / (j1 - j0);

        if (slope != 1 && slope != -1){
            goto err;
        } 
        

        if (!blocked(j0, j1, i0, i1)){
            goto mov;
        }

        else{
            goto err;
        }

    }


    if (type == QUEEN){
        int slope = 0;

        //again, this avoids dividing by 0
        if (j0 != j1){
            slope = (i1 - i0) / (j1 - j0);
        }
        
        /*checks if path matches either the rook or bishop movement patterns
          since a queen is basically a rook and bishop powers combined together*/

        if (i0 != i1 && j0 != j1 && slope != 1 && slope != -1){
            goto err;
        }


        if (blocked(j0, j1, i0, i1)){
            goto err;
        }


        else{
            goto mov;
        }

    }

    if (type == KING){

        //difference between the x coordinates and y coordinates
        int di = i1 - i0;
        int dj = j1 - j0;

        if (i0 == i1 || j0 == j1){
            //if its a vertical or horizontal move, only square difference allowed

            if (di != 1 && dj != 1 && di != -1 && dj != -1){
                goto err;
            }

        }

        //these check if the move is a diagonal move
        else if ((di * dj != 1) && (di * dj != -1)){
            goto err;
        }

        goto mov;   

    }

err:
    down_write(&resp_lock);
    response = ILLMOVE;
    resplen = 8;
    up_write(&resp_lock);

    return false;



mov:
    /*just change the piece type of the moved piece if its being promoted*/
    down_write(&board_lock);

    if (color == WHITE){
        i = wkingpos[0];
        j = wkingpos[1];
    }

    else{
        i = bkingpos[0];
        j = bkingpos[1];
    }

    if (promoted){
        src = (char *) kmalloc (2, GFP_KERNEL);
        promoted_pieces[index] = src;
        index++;
        src[0] = color;
        src[1] = promoted_type;
    }
    
    board[j1][i1] = src;
    board[j0][i0] = EMPTY;

    moves++;

    up_write(&board_lock);

    /*we're acquiring a read lock in order to call check()
      and see if the move the playing side is making puts the 
      king in check. If it does, we call a write lock for the 
      board again to reverse the move we made and goto err to 
      return ILLMOVE error*/

    if (check(i, j, color)){

        down_write(&board_lock);

        board[j1][i1] = dest;
        board[j0][i0] = src;

        up_write(&board_lock);

        goto err;
        
    }

    

    down_write(&board_lock);
    
    if (type == KING){
        if (color == WHITE){
            wkingpos[0] = j1;
            wkingpos[1] = i1;
        }

        else{
            bkingpos[0] = j1;
            bkingpos[1] = i1;
        }
    }
    
    turn = comp;

    up_write(&board_lock);


    down_write(&resp_lock);
    response = OK;
    resplen = 3;
    up_write(&resp_lock);


    return true;
    
}


static ssize_t game_read(struct file *pfile, char __user *usr, size_t len, loff_t *offset)
{

    ssize_t bytes_read = 0;
    unsigned long uncopied = 0;
    
    if (access_ok(usr, len) == EFAULT){
        return -EFAULT;
    }


    //allocate command buffer and copy from user  
    down_read(&resp_lock);
   
    uncopied = copy_to_user(usr, response, resplen);    
    bytes_read = (ssize_t) resplen;

    up_read(&resp_lock);

    if (uncopied != 0){
        return -EFAULT;
    }


    return bytes_read;

}


static ssize_t game_write(struct file *pfile, const char __user *usr, size_t len, loff_t *offset)
{   
    
    char *str = NULL;
    char cmd = '\0';
    unsigned long uncopied = 0;
    
    if (access_ok(usr, len) == EFAULT){
        return -EFAULT;
    } 

    //length of string must be at least three, including '\n', to be valid cmd
    if (len <= 2){

        down_write(&resp_lock);
        response = UNKCMD;
        resplen = 7;
        up_write(&resp_lock);
        
        return len;   
         
    }

    
    //allocate command buffer and copy from user    
    str = (char *) kmalloc(len, GFP_KERNEL);

    if (str == NULL){
        //kfree(str);
        return -ENOMEM;
    }

    uncopied = copy_from_user(str, usr, len);

    //free and return error if something goes wrong
    if (uncopied != 0){
        kfree(str);
        return -EFAULT;
    }


    if(!validate(str, len)){
        kfree(str);
        return len;
    }


    cmd = str[1];

    //initializes a new game/resets game

    if(cmd == '0'){
        
        down_write(&board_lock);
        reset(str[3]);
        up_write(&board_lock);

        down_write(&resp_lock);
        response = OK;
        resplen = 3;
        up_write(&resp_lock);

    }


    //returns board string
    if (cmd == '1'){
        /*this is the one exception we are using board_lock
         for the response variable because it involves the board string
         not a response string
        */

        
        down_read(&board_lock);
        down_write(&resp_lock);

        if (games == 0){
            response = NOGAME;
            resplen = 7;
        }

        else{
            print();
            response = boardstr;
            resplen = 129;
        }
    
        up_write(&resp_lock);
        up_read(&board_lock);

    }


    //human moves
    if (cmd == '2'){

        int i = 0, j = 0;
        
        down_read(&board_lock);
        
        if (!game_initialized){

            down_write(&resp_lock);
            response = NOGAME;
            resplen = 7;
            up_write(&resp_lock);

            up_read(&board_lock);

            kfree(str);
            return len;

        }


        if (turn != human){

            down_write(&resp_lock);
            response = OOT;
            resplen = 4;
            up_write(&resp_lock);

            up_read(&board_lock);
            
            kfree(str);
            return len;

        }


        if (human == WHITE){
            i = bkingpos[0];
            j = bkingpos[1];
        }

        else{
            i = wkingpos[0];
            j = wkingpos[1]; 
        }
        
        /*
        printk("i is: %d\n", i);
        printk("j is: %d\n", j);
        */

        up_read(&board_lock);

        validateMove(str, len);
        check_or_mate(i, j, comp);
        
    }


    //computer moves
    if (cmd == '3'){

        int i = 0, j = 0;

        down_read(&board_lock);

        if (!game_initialized){

            down_write(&resp_lock);
            response = NOGAME;
            resplen = 7;
            up_write(&resp_lock);

            up_read(&board_lock);

            kfree(str);
            return len;

        }

        if (turn != comp){

            down_write(&resp_lock);
            response = OOT;
            resplen = 4;
            up_write(&resp_lock);

            up_read(&board_lock);

            kfree(str);
            return len;

        }


        if (comp == WHITE){
            i = bkingpos[0];
            j = bkingpos[1];
        }

        else{
            i = wkingpos[0];
            j = wkingpos[1]; 
        }

        up_read(&board_lock);

        computer_move();
        check_or_mate(i, j, human);

    }


    //resigns game
    if (cmd == '4'){

        down_read(&board_lock);
        
        /*if game has already ended in Mate, simply return;
          the project says resign command should return MATE 
          as the response string if the game has already ended
          in a mate*/
          
        down_read(&resp_lock);

        if (mated){
            response = MATE;
            resplen = 5;

            up_read(&resp_lock);
            up_read(&board_lock);

            kfree(str);
            return len;

        }

        up_read(&resp_lock);


        if (!game_initialized){

            down_write(&resp_lock);
            response = NOGAME;
            resplen = 7;
            up_write(&resp_lock);

            up_read(&board_lock);

            kfree(str);
            return len;

        }

        if (turn != human){

            down_write(&resp_lock);
            response = OOT;
            resplen = 4;
            up_write(&resp_lock);

            up_read(&board_lock);
            
            kfree(str);
            return len;

        }

        game_initialized = false;
        
        down_write(&resp_lock);
        response = OK;
        resplen = 3;
        up_write(&resp_lock);

        up_read(&board_lock);

    } 


    kfree(str);
    return len;

}


static struct file_operations gamefops = {
    .owner = THIS_MODULE,
    .read = game_read,
    .write = game_write,
};


static struct miscdevice game = {
    //dynamically choose a minor number
    .minor = MISC_DYNAMIC_MINOR,

    // /dev/chess
    .name = "chess",

    .fops = &gamefops,

    //0666 gives read/write access to the user (owner), group, and others that have access to the file
    .mode = 0666,
};


static int __init game_init(void)
{
    int i;
    int rv = misc_register(&game);


    if (rv){
        printk("Device registration failed\n");
        return rv;
    }

    init_rwsem(&resp_lock);
    init_rwsem(&board_lock);

    for (i = 0; i < 8; i++){
        memcpy(board[i], empty, 8 * sizeof(char *));
    }

    printk("initialized\n");
    
    return 0;

}


static void __exit game_exit(void)
{

    int i;

    //delete all the promoted pieces stored and set to null
    for (i = 0; i < 16; i++){
        if (promoted_pieces[i] != NULL){
            kfree(promoted_pieces[i]);
            promoted_pieces[i] = NULL;
        }
    }

    misc_deregister(&game);

    printk("exiting\n");

}


module_init(game_init);
module_exit(game_exit);