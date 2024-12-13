---- MODULE spec ----
EXTENDS TLC, Naturals

VARIABLES 
    board, \* A 3x3 tic-tac-toe board
    next_turn \* who goes next

vars == <<board, next_turn>>

Pieces == {"X", "O", "_"} \* "_" represents a blank square

Init ==
    /\ next_turn = "X" \* X always goes first
    /\ board = [i \in 1..3 |-> [j \in 1..3 |-> "_"]] \* Every space in the board starts blank

Move(player) ==
    \E i \in 1..3:
        \E j \in 1..3: \* There exists some position i, j in the board
            /\ board[i][j] = "_" \* Where the board position is empty
            \* The next state of the board is the board with the player in the position
            /\ board' = [board EXCEPT ![i][j] = player] 

MoveX ==
    /\ next_turn = "X" \* Action enabled only then it's X's turn
    /\ Move("X")
    /\ next_turn' = "O" \* next_turn wil be "0" in the next state

MoveO ==
    /\ next_turn = "O" \* Action enabled only then it's O's turn
    /\ Move("O")
    /\ next_turn' = "X" \* next_turn wil be "X" in the next state

\* In every state, it'll be X's turn or O's turn
Next == MoveX \/ MoveO

Spec == Init /\ [][Next]_vars

WinningPositions == {
    \* Horizontal wins
    {<<1, 1>>, <<1, 2>>, <<1, 3>>},
    {<<2, 1>>, <<2, 2>>, <<2, 3>>},
    {<<3, 1>>, <<3, 2>>, <<3, 3>>},
    \* Vertical wins
    {<<1, 1>>, <<2, 1>>, <<3, 1>>},
    {<<1, 2>>, <<2, 2>>, <<3, 2>>},
    {<<1, 3>>, <<2, 3>>, <<3, 3>>},
    \* Diagonal wins
    {<<1, 1>>, <<2, 2>>, <<3, 3>>},
    {<<3, 1>>, <<2, 2>>, <<1, 3>>}
}

Won(player) ==
    \* A player has won if there exists a winning position
    \E winning_position \in WinningPositions:
        \* Where all the positions
        \A position \in winning_position:
            \* Are ocuppied by the player
            board[position[1]][position[2]] = player

XHasNotWon == ~Won("X")
OHasNotWon == ~Won("O")

BoardFilled ==
    \* There does not exist
    ~\E i, j \in 1..3:
        \* An empty space in the board
        LET space == board[i][j] IN 
        space = "_"

\* It's not a stalemate if one player has won or the board is not filled
NotStalemate ==
    \* \/ Won("X")
    \* \/ Won("O")
    \/ ~BoardFilled
====