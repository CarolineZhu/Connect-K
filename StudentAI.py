# from typing import List
from copy import deepcopy
from random import randint
from BoardClasses import Move
from BoardClasses import Board
from enum import Enum
from itertools import product

_MAX_DEPTH = 4

_PARA = 3


class Point(Move):
    def __init__(self, row: int, col: int):
        super().__init__(col=col, row=row)

    def __add__(self, other: Move):
        result = Point(row=self.row + other.row, col=self.col + other.col)
        return result

    def __radd__(self, other: Move):
        return Point(row=self.row + other.row, col=self.col + other.col)

    def __sub__(self, other: Move):
        return Point(row=self.row - other.row, col=self.col - other.col)

    def __neg__(self):
        return Point(row=-self.row, col=-self.col)

    def __ne__(self, other: Move):
        return self.row != other.row or self.col != other.col

    def __str__(self):
        return "(" + self.row + "," + self.col + ")"


class Player(Enum):
    no = 0
    me = 1
    op = 2


class Dir:
    ul = Point(-1, -1)  # type: Point
    u = Point(-1, 0)  # type: Point
    ur = Point(-1, 1)  # type: Point
    r = Point(0, 1)  # type: Point
    dr = Point(1, 1)  # type: Point
    d = Point(1, 0)  # type: Point
    dl = Point(1, -1)  # type: Point
    l = Point(0, -1)  # type: Point
    N = Point(0, 0)  # type: Point


half_dir = [Dir.ul, Dir.u, Dir.ur, Dir.r]
all_dir = [Dir.ul, Dir.u, Dir.ur, Dir.r, Dir.dr, Dir.d, Dir.dl, Dir.l]


class InvalidMoveError(Exception):
    pass


class HashBoard(Board):
    my_hash = []
    op_hash = []
    init = False

    def __init__(self, col: int, row: int, k: int, g: int):
        super().__init__(col, row, k, g)
        self.board = [[Player.no for _ in range(col)] for _ in range(row)]
        if not HashBoard.init:
            HashBoard.my_hash = [[randint(0, 1 << 64) for _ in range(col)] for _ in range(row)]
            HashBoard.op_hash = [[randint(0, 1 << 64) for _ in range(col)] for _ in range(row)]
            HashBoard.init = True
        self.cur_hash = 0

    def make_internal_move(self, move: Move, player: Player):
        self.cur_hash ^= (HashBoard.my_hash if player == Player.me else HashBoard.op_hash)[move.row][move.col]

    def __hash__(self):
        return self.cur_hash

    def __eq__(self, other: 'HashBoard'):
        for i, j in product(range(self.row), range(self.col)):
            if self.board[i][j] != other.board[i][j]:
                return False
        return True


class MyBoard(HashBoard):
    def __init__(self, col: int, row: int, k: int, g: int):
        super().__init__(col, row, k, g)
        self.move = []  # type: List[Move]
        self.move_player = []  # type: List[Player]
        self.me_point_score = [[[0 for _ in range(col)] for _ in range(row)] for _ in range(4)]
        self.op_point_score = [[[0 for _ in range(col)] for _ in range(row)] for _ in range(4)]
        self.has_neighbor = [[[False for _ in range(col)] for _ in range(row)] for _ in range(8)]
        self.has_indirect_neighbor = [[[False for _ in range(col)] for _ in range(row)] for _ in range(8)]
        self.MIN = (-1 << (k + 2) * _PARA) * k * k * 4
        self.MAX = -self.MIN

    def is_inside(self, move: Move) -> bool:
        return 0 <= move.col < self.col and 0 <= move.row < self.row

    def is_on_board(self, move: Move, direction: Point) -> bool:
        return self.is_inside(move) and not self.is_inside(move + direction)

    def get_available_points_ng(self, player: Player):
        children = []
        for i, j in product(range(self.row), range(self.col)):
            if self.board[i][j] != Player.no:
                continue
            cur_point = Point(i, j)
            if not self.not_isolate(cur_point):
                continue
            point_score = self.MIN
            for n in range(4):
                point_score = max(point_score, self.get_point_score(cur_point, player, n))
            children.append((point_score, cur_point))
        children.sort(key=lambda x: x[0], reverse=True)
        return children

    def get_available_points_g(self, player: Player):
        children = []
        for i in range(self.col):
            for j in range(self.row - 1, -1, -1):
                if self.board[j][i] == Player.no:
                    cur_point = Point(j, i)
                    if not self.not_isolate(cur_point):
                        continue
                    point_score = self.MIN
                    for n in range(4):
                        point_score = max(point_score, self.get_point_score(cur_point, player, n))
                    children.append((point_score, cur_point))
                    break

        children.sort(key=lambda x: x[0], reverse=True)
        return children

    def min_search(self, depth: int, alpha: int, beta: int) -> (int, Point):
        player = Player.op
        return self.min_iter(player, alpha, beta, depth)

    def min_iter(self, player: Player, alpha: int, beta: int, depth: int) -> (int, Point):
        min_score = self.MAX
        min_move = None  # type: Point
        children = self.get_available_points_ng(player) if self.g == 0 else self.get_available_points_g(player)
        for _, cur_point in children:
            self.make_internal_move(cur_point, player)
            if Cache.has(self):
                cache_depth, cache_score = Cache.get(self)
                if cache_depth >= depth:
                    self.del_internal_move()
                    return cache_score, cur_point
            if depth == 0:
                evaluate = self.evaluate()
            else:
                evaluate, move = self.max_search(depth - 1, alpha, beta)
            Cache.add(self, evaluate, depth)
            if evaluate < min_score:
                min_score = evaluate
                min_move = cur_point
                if evaluate < beta:
                    beta = evaluate
                    if beta <= alpha:
                        self.del_internal_move()
                        break
            self.del_internal_move()
        return min_score, min_move

    def max_search(self, depth: int, alpha: int, beta: int) -> (int, Point):
        player = Player.me
        return self.max_iter(player, alpha, beta, depth)

    def max_iter(self, player: Player, alpha: int, beta: int, depth: int) -> (int, Point):
        max_score = self.MIN
        max_move = None  # type: Point
        children = self.get_available_points_ng(player) if self.g == 0 else self.get_available_points_g(player)
        for _, cur_point in children:
            self.make_internal_move(cur_point, player)
            if Cache.has(self):
                cache_depth, cache_score = Cache.get(self)
                if cache_depth >= depth:
                    self.del_internal_move()
                    return cache_score, cur_point
            if depth == 0:
                evaluate = self.evaluate()
            else:
                evaluate, move = self.min_search(depth - 1, alpha, beta)
            Cache.add(self, evaluate, depth)
            if evaluate > max_score:
                max_score = evaluate
                max_move = cur_point
                if evaluate > alpha:
                    alpha = evaluate
                    if alpha >= beta:
                        self.del_internal_move()
                        break

            self.del_internal_move()
        return max_score, max_move

    def update_evaluate(self, move: Move):
        point = Point(move.row, move.col)
        self.evaluate_point(point, Player.me)
        self.evaluate_point(point, Player.op)
        for i in range(4):
            tmp = point
            direction = half_dir[i]
            while True:
                tmp += direction
                if self.is_inside(tmp):
                    self.evaluate_point(tmp, Player.me, i)
                    self.evaluate_point(tmp, Player.op, i)
                else:
                    break

            tmp = point
            while True:
                tmp -= direction
                if self.is_inside(tmp):
                    self.evaluate_point(tmp, Player.me, i)
                    self.evaluate_point(tmp, Player.op, i)
                else:
                    break

    def del_internal_move(self):
        cur_move = self.move.pop()
        cur_player = self.move_player.pop()
        self.board[cur_move.row][cur_move.col] = Player.no
        self.update_evaluate(cur_move)
        # update neighbor
        for i in range(8):
            tmp = cur_move + all_dir[i]
            if self.is_inside(tmp):
                self.has_neighbor[i][tmp.row][tmp.col] = True
                tmp += all_dir[i]
                if self.is_inside(tmp):
                    self.has_indirect_neighbor[i][tmp.row][tmp.col] = True
        # update hash
        super().make_internal_move(cur_move, cur_player)

    def evaluate(self) -> int:
        result = 0
        for i, x, y in product(range(4), range(self.row), range(self.col)):
            result += self.me_point_score[i][x][y]
            result -= self.op_point_score[i][x][y]
        return result

    def evaluate_point(self, point: Point, player: Player, direction_index: int = None) -> None:
        matrix = self.me_point_score if player == Player.me else self.op_point_score
        if self.board[point.row][point.col] != player:
            for i in range(4):
                matrix[i][point.row][point.col] = 0

        if direction_index is None:
            if self.board[point.row][point.col] != player:
                for i in range(4):
                    matrix[i][point.row][point.col] = 0
            else:
                for i in range(4):
                    self.evaluate_point(point, player, i)
        else:
            if self.board[point.row][point.col] != player:
                matrix[direction_index][point.row][point.col] = 0
            else:
                matrix[direction_index][point.row][point.col] = self.get_point_score(point, player, direction_index)

    def not_isolate(self, point: Point) -> bool:
        for i in range(8):
            if self.has_neighbor[i][point.row][point.col] or self.has_indirect_neighbor[i][point.row][point.col]:
                return True
        return False

    def get_point_score(self, point: Point, player: Player, direction_index: int) -> int:
        opposite = Player.op if player == Player.me else Player.me
        direction = half_dir[direction_index]
        count = 1
        block = 0
        empty = 0

        tmp = point
        continuous = True
        while True:
            tmp += direction
            if not self.is_inside(tmp):
                break
            if self.is_on_board(tmp, direction):
                if continuous:
                    block += 1
                break
            tmp_occupied = self.board[tmp.row][tmp.col]
            if tmp_occupied == player and continuous:
                count += 1
            elif tmp_occupied == opposite:
                if continuous:
                    block += 1
                break
            else:
                empty += 1
                continuous = False
                if empty + count >= self.k:
                    break

        tmp = point
        continuous = True
        while True:
            tmp -= direction
            if not self.is_inside(tmp):
                break
            if self.is_on_board(tmp, direction):
                if continuous:
                    block += 1
                break
            tmp_occupied = self.board[tmp.row][tmp.col]
            if tmp_occupied == player and continuous:
                count += 1
            elif tmp_occupied == opposite:
                if continuous:
                    block += 1
                break
            else:
                empty += 1
                continuous = False
                if empty + count >= self.k:
                    break

        if count >= self.k:
            score = 1 << (_PARA * (self.k - 1))
        elif count + empty < self.k or block == 2:
            score = 0
        elif block == 0:
            score = 1 << (_PARA * count)
        else:
            score = 1 << (_PARA * (count - 1))
        return score


class Cache:
    cache = {}

    @classmethod
    def add(cls, board: HashBoard, score: int, depth: int) -> None:
        cls.cache[deepcopy(board)] = (depth, score)

    @classmethod
    def has(cls, board: HashBoard):
        return board in cls.cache

    @classmethod
    def get(cls, board: HashBoard) -> (int, int):
        return cls.cache.get(board)


class BoardG(MyBoard):
    def __init__(self, col: int, row: int, k: int):
        super().__init__(col, row, k, 1)

    def make_internal_move(self, move: Move, player: Player) -> None:
        for i in range(self.row - 1, -1, -1):
            if self.board[i][move.col] == Player.no:
                self.board[i][move.col] = player
                move.row = i
                self.move.append(move)
                self.move_player.append(player)
                break
            try:
                i > 0
            except InvalidMoveError:
                print("Invalid Move!")

        for i in range(8):
            tmp = move + all_dir[i]
            if self.is_inside(tmp):
                self.has_neighbor[i][tmp.row][tmp.col] = True
                tmp += all_dir[i]
                if self.is_inside(tmp):
                    self.has_indirect_neighbor[i][tmp.row][tmp.col] = True

        super().make_internal_move(move, player)


class BoardNG(MyBoard):
    def __init__(self, col: int, row: int, k: int):
        super().__init__(col, row, k, 0)

    def make_internal_move(self, move: Move, player: Player) -> None:
        try:
            self.board[move.row][move.col] == Player.no
        except InvalidMoveError:
            print("Invalid Move!")
        self.board[move.row][move.col] = player
        self.move.append(move)
        self.move_player.append(player)
        self.update_evaluate(move)
        # update neighbor
        for i in range(8):
            tmp = move + all_dir[i]
            if self.is_inside(tmp):
                self.has_neighbor[i][tmp.row][tmp.col] = True
                tmp += all_dir[i]
                if self.is_inside(tmp):
                    self.has_indirect_neighbor[i][tmp.row][tmp.col] = True
        # update hash
        super().make_internal_move(move, player)


# The following part should be completed by students.
# Students can modify anything except the class name and exisiting functions and varibles.
class StudentAI:
    col = 0
    row = 0
    k = 0
    g = 0

    def __init__(self, col: int, row: int, k: int, g: int):
        self.col = col
        self.row = row
        self.k = k
        self.board = BoardNG(col, row, k) if g == 0 else BoardG(col, row, k)  # type: MyBoard
        self.get_move = self._get_move_ng if g == 0 else self._get_move_g

    def iterative_deepening_search(self, move: Move) -> Move:
        pass

    def _get_move_g(self, move: Move) -> Move:
        global _MAX_DEPTH
        _MAX_DEPTH = 6
        if Point(-1, -1) == move:
            result = Move(int(self.col / 2), self.row - 1)
        else:
            self.board.make_internal_move(move, Player.op)
            result = self.board.max_search(_MAX_DEPTH, self.board.MIN, self.board.MAX)[1]
        self.board.make_internal_move(result, Player.me)
        return result

    def _get_move_ng(self, move: Move) -> Move:
        global _MAX_DEPTH
        _MAX_DEPTH = 4
        if Point(-1, -1) == move:
            result = Move(int(self.col / 2), int(self.row / 2))
        else:
            self.board.make_internal_move(move, Player.op)
            result = self.board.max_search(_MAX_DEPTH, self.board.MIN, self.board.MAX)[1]
        self.board.make_internal_move(result, Player.me)
        return result
