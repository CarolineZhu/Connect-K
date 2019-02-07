from random import randint
from BoardClasses import Move
from BoardClasses import Board
#The following part should be completed by students.
#Students can modify anything except the class name and exisiting functions and varibles.
class StudentAI():
    col = 0
    row = 0
    k = 0
    g = 0

    def __init__(self,col,row,k,g):
        self.g = g
        self.col = col
        self.row = row
        self.k = k
        self.board = Board(col,row,k,g)

    def get_move(self,move):
        if self.g == 0:
            return Move(randint(0,self.col-1),randint(0,self.row-1))
        else:
            return Move(randint(0,self.col-1),0)
