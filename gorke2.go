///////////////////////////////////////////////
// main package

package main

///////////////////////////////////////////////

///////////////////////////////////////////////
//  : 
// ->  : 
// <-  : 

///////////////////////////////////////////////

///////////////////////////////////////////////
// imports

import (
	"fmt"
	"os"
	"bufio"
	"text/scanner"
	"strings"
	"sync"
	"time"
	"math/rand"
	"sort"
	"strconv"
)

///////////////////////////////////////////////

const TEST=true
//const TEST=false

///////////////////////////////////////////////
// types
///////////////////////////////////////////////

// types defining a piece
type TPiece byte
type TPieceType byte
type TColor byte
// end types defining a piece

// types defining a square
type TSquare byte
type TFile byte
type TRank byte
// end types defining a square

// types for the board and move generation
type TMoveTableKey struct {
	Sq TSquare
	P TPiece
}

type TMoveDescriptor struct {
	To TSquare
	NextVector int
	EndPiece bool
}

type TMove struct {
	From TSquare
	To TSquare
	Piece TPiece
	CapPiece TPiece
	Eval int
	IsForwardKingMove bool
	IsAlphaBetaBestMove bool
}

type TPosition struct {
	Rep [BOARD_SIZE]byte
	Turn TColor
	Depth int
}

type TBoard struct {
	Pos TPosition
	CurrentSq TSquare
	CurrentPiece TPiece
	CurrentPtr int
	CurrentMove TMove
	HasBestMove bool
	BestMoveDone bool
	BestMove TMove
	Material [2]int
	KingPositions [2] TSquare
	BaseDepth int
}
// end board and move generation types

// game types
type TMoveList []TMove

type TGame struct {
	B TBoard
	Moves TMoveList
}
// end game types

// book types
type TNode struct {
	Moves TMoveList
}
// end book types

///////////////////////////////////////////////
// end types
///////////////////////////////////////////////

///////////////////////////////////////////////
// constants
///////////////////////////////////////////////

const UCI_INTRO_MESSAGE="gorke2 racing kings chess variant engine"

const RESPONSE_TO_UCI_COMMAND=
	"id name gorke2\n"+
	"id author golang\n"+
	"\n"+
	"option name MultiPV type spin default 1 min 1 max 500\n"+
	"option name MateSearch type check default true\n"+
	"option name Randomness type spin default 10 min 0 max 100\n"+
	"option name RandomSearch type check default false\n"+
	"option name Branching type spin default 50 min 0 max 100\n"+
	"option name ClearHash type button\n"+
	"option name KingAdvanceValue type spin default 400 min 0 max 1000\n"+
	"option name KnightValue type spin default 300 min 0 max 1000\n"+
	"option name BishopValue type spin default 300 min 0 max 1000\n"+
	"option name RookValue type spin default 500 min 0 max 1000\n"+
	"option name QueenValue type spin default 700 min 0 max 1000\n"+
	"option name RandomDepthOdd type spin default 3 min 0 max 10\n"+
	"option name RandomDepthEven type spin default 4 min 0 max 10\n"+
	"option name PruneThresoldLow type spin default 0 min 0 max 10\n"+
	"option name PruneThresoldHigh type spin default 10 min 0 max 10\n"+
	"option name PruneFromDepth type spin default 4 min 0 max 10\n"+
	"option name PruneDepth type spin default 1 min 0 max 10\n"+
	"uciok\n"

const MAX_SEARCH_DEPTH=100

///////////////////////////////////////////////
// constants defining a piece
///////////////////////////////////////////////

const IS_SLIDING  = 1<<6
const IS_STRAIGHT = 1<<5
const IS_DIAGONAL = 1<<4
const IS_SINGLE   = 1<<3
const IS_JUMPING  = 1<<2
const IS_WHITE    = 1<<1
const IS_BLACK    = 1<<0

const IS_PIECE    = IS_WHITE|IS_BLACK

const TYPE_MASK   = IS_SLIDING|IS_STRAIGHT|IS_DIAGONAL|IS_SINGLE|IS_JUMPING

const WHITE       = IS_WHITE

const COLOR_MASK  = IS_PIECE

const BLACK       = IS_BLACK

const KING        = IS_STRAIGHT|IS_DIAGONAL|IS_SINGLE
const QUEEN       = IS_STRAIGHT|IS_DIAGONAL|IS_SLIDING
const ROOK        = IS_STRAIGHT|IS_SLIDING
const BISHOP      = IS_DIAGONAL|IS_SLIDING
const KNIGHT      = IS_JUMPING|IS_SINGLE

const NO_PIECE    = 0
const NO_COLOR    = 0

///////////////////////////////////////////////
// end constants defining a piece
///////////////////////////////////////////////

///////////////////////////////////////////////
// constants defining a square
///////////////////////////////////////////////

const BOARD_WIDTH         = 8
const BOARD_WIDTHL        = BOARD_WIDTH-1

const BOARD_HEIGHT        = BOARD_WIDTH
const BOARD_HEIGHTL       = BOARD_HEIGHT-1

const BOARD_SIZE          = BOARD_WIDTH * BOARD_HEIGHT
const BOARD_SIZEL         = BOARD_SIZE-1

const NO_SQUARE           = BOARD_SIZE

const BOARD_SHIFT         = 3

const FILE_MASK           = BOARD_WIDTHL
const RANK_MASK           = FILE_MASK << BOARD_SHIFT

///////////////////////////////////////////////
// end constants defining a square
///////////////////////////////////////////////

///////////////////////////////////////////////
// board constants
///////////////////////////////////////////////

const MOVE_TABLE_MAX_SIZE = 20000

const MAX_MULTIPV         = 500

const START_FEN         = "8/8/8/8/8/8/krbnNBRK/qrbnNBRQ w - - 0 1"

const DRAW_SCORE        = 0

const MATE_LIMIT        = 9000
const MATE_SCORE        = 10000
const INFINITE_SCORE    = 15000
const INVALID_SCORE     = 20000

var PIECE_VALUES=map [TPieceType]int{
	NO_PIECE : 0,
	KING : 0,
	QUEEN : 700,
	ROOK : 500,
	BISHOP : 300,
	KNIGHT : 300}

var KING_ADVANCE_VALUE = 400

const INDEX_OF_WHITE    = 1
const INDEX_OF_BLACK    = 0

///////////////////////////////////////////////
// end board constants
///////////////////////////////////////////////

///////////////////////////////////////////////
// end constants
///////////////////////////////////////////////

///////////////////////////////////////////////
// global variables
///////////////////////////////////////////////

// variables that can be set through the setoption command
// perform mate search
var MateSearch bool=true
// perform random search
var RandomSearch bool=false
// randomness of eval
var Randomness int=10
// branching probability
var Branching int=50
// pruning thresold lower
var PruneThresoldLow int=0
// pruning thresold upper
var PruneThresoldHigh int=10
// pruning thresold for max depth
var PruneFromDepth int=4
// pruning depth
var PruneDepth int=1
// radnom depth odd
var RandomDepthOdd int=3
// radnom depth even
var RandomDepthEven int=4

// scanner for reading tokens from a string
var Scanner scanner.Scanner
// commandline read from stdin
var Commandline string
// token read from commandline
var Token string
// bool parsed from Token
var B bool
// int parsed from Token
var I int
// reader to read from stdin
var Reader = bufio.NewReader(os.Stdin)
// command read from command line
var Command string=""

// all piece types
var ALL_PIECE_TYPES=[]TPieceType{KING,QUEEN,ROOK,BISHOP,KNIGHT}
// move table
var MoveTable [MOVE_TABLE_MAX_SIZE]TMoveDescriptor
// move table pointers
var MoveTablePtrs=make(map[TMoveTableKey]int)

// game
var G TGame

// random number generator
var Rand=rand.New(rand.NewSource(time.Now().UnixNano()))

// alphabeta move cache
var BestMoves=make(map[TPosition]TMove)

// nodes
var Nodes=make(map[TPosition]TNode)

// base alpha
var BaseAlpha=-INFINITE_SCORE
// alphabeta evals
var AlphaBetaEvals [MAX_MULTIPV]int
// alphabeta moves
var AlphaBetaMoves [MAX_MULTIPV]TMove
// num alphabeta moves
var NumAlphaBetaMoves=0

// number of threads used in alphabeta search
var NumThreads=MAX_MULTIPV

// abort search
var AbortSearch=false
// alphabeta ready
var SearchReady=false
// starting time of timer
var StartingTime=time.Now().UTC()
// nodes for alphabeta searc
var SearchNodes=0
// search depth
var SearchDepth=0
// depth
var Depth=0
// nps
var Nps int64=0
// time
var Time int64=0
// eval
var Eval=0
// pv
var Pv=""
// multipv
//var MultiPV=MAX_MULTIPV
var MultiPV=1
// multipv index
var MultiPVIndex=1
// score
var Score=""
// best move algeb
var BestMoveAlgeb=""

///////////////////////////////////////////////
// end global variables
///////////////////////////////////////////////

///////////////////////////////////////////////
// functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// Init : initialization

func Init() {
	InitMoveTable()
	G.SetFromFen(START_FEN)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Abs : absolute value of int
// -> value int : value
// <- int : absolute value

func Abs(value int) int {
	if value>=0 {
		return value
	}
	return -value
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// InitMoveTable : initialize move table

func InitMoveTable() {
	ptr:=0
	for _,pt := range ALL_PIECE_TYPES {
		for sq:=0; sq<BOARD_SIZE; sq++ {
			
			MoveTablePtrs[TMoveTableKey{TSquare(sq), FromTypeAndColor(TPieceType(pt),BLACK)}]=ptr
			MoveTablePtrs[TMoveTableKey{TSquare(sq), FromTypeAndColor(TPieceType(pt),WHITE)}]=ptr

			for df:=-2; df<=2; df++ {
				for dr:=-2; dr<=2; dr++ {
					vector_ok:=false
					dfabs:=Abs(df)
					drabs:=Abs(dr)
					prodabs:=dfabs*drabs
					sumabs:=dfabs+drabs
					if (pt&IS_JUMPING)!=0 {
						vector_ok=vector_ok||(prodabs==2)
					}
					if (pt&IS_STRAIGHT)!=0 {
						vector_ok=vector_ok||(sumabs==1)
					}
					if (pt&IS_DIAGONAL)!=0 {
						vector_ok=vector_ok||(prodabs==1)
					}
					if vector_ok {
						ok:=true
						f:=int(TSquare(sq).File())
						r:=int(TSquare(sq).Rank())
						vector_start:=ptr
						for ok {
							f+=df
							r+=dr
							if FileRankOk(f,r) {
								tsq:=FromFileRank(TFile(f),TRank(r))
								MoveTable[ptr].To=tsq
								MoveTable[ptr].EndPiece=false
								ptr++
							} else {
								ok=false
							}
							if (pt&IS_SLIDING)==0 {
								ok=false
							}
						}						
						for vector_next_ptr:=vector_start; vector_next_ptr<ptr; vector_next_ptr++ {
							MoveTable[vector_next_ptr].NextVector=ptr
						}
					}
				}
			}

			MoveTable[ptr].EndPiece=true
			ptr++
		}
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// piece functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// Type : determine the type of the piece
// -> p TPiece : piece
// <- TPieceType : piece type

func (p TPiece) Type() TPieceType {
	return TPieceType(p&TYPE_MASK)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Color : determine the color of the piece
// -> p TPiece : piece
// <- TColor : piece color

func (p TPiece) Color() TColor {
	return TColor(p&COLOR_MASK)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// InvColorOf : determine the inverse color of some color
// -> c TColor : color
// <- TColor : inverse color

func InvColorOf(c TColor) TColor {
	c&=COLOR_MASK
	if c==WHITE { return BLACK }
	if c==BLACK { return WHITE }
	return NO_COLOR
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FromTypeAndColor : create a piece from type and color
// -> t TPieceType : piece type
// -> c TColor : piece color
// <- TPiece : the created piece of type t and color c

func FromTypeAndColor(t TPieceType, c TColor) TPiece {
	return TPiece(byte(t)|byte(c))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToFenChar : determine the fen char of the piece
// -> p TPiece : piece
// <- byte : fen char of the piece

func ToFenChar(p TPiece) byte {
	var fenchar byte

	switch p.Type() {
		case KING : fenchar='k'
		case QUEEN : fenchar='q'
		case ROOK : fenchar='r'
		case BISHOP : fenchar='b'
		case KNIGHT : fenchar='n'
		default : return ' '
	}

	if p.Color()==WHITE {
		fenchar-='a'-'A'
	}

	return fenchar
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FromFenChar : create a piece from a fen char
// -> fenchar byte : fen char to create the piece from
// <- TPiece : piece created from the fen char

func FromFenChar(fenchar byte) TPiece {
	var c TColor=WHITE

	var t TPieceType

	switch fenchar {
		case 'K' : t=KING
		case 'k' : t=KING; c=BLACK
		case 'Q' : t=QUEEN
		case 'q' : t=QUEEN; c=BLACK
		case 'R' : t=ROOK
		case 'r' : t=ROOK; c=BLACK
		case 'B' : t=BISHOP
		case 'b' : t=BISHOP; c=BLACK
		case 'N' : t=KNIGHT
		case 'n' : t=KNIGHT; c=BLACK
		default : return NO_PIECE
	}

	return FromTypeAndColor(t,c)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end piece functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// square functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// File : file of a square
// -> sq TSquare : square
// <- TFile : file

func (sq TSquare) File() TFile {
	return TFile(byte(sq)&FILE_MASK)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Rank : rank of a square
// -> sq TSquare : square
// <- Trank : rank

func (sq TSquare) Rank() TRank {
	return TRank((byte(sq)&RANK_MASK)>>BOARD_SHIFT)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Rank : rank of square
// -> sq TSquare : square
// <- TRank : rank

func (sq TSquare) RankOf() TRank {
	return TRank((byte(sq)&RANK_MASK)>>BOARD_SHIFT)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FileOk : file is valid
// -> f int : file as int ( can be negative )
// <- bool : true = file is ok, false = file out of range

func FileOk(f int) bool {
	return (f>=0) && (f<BOARD_WIDTH)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// RankOk : rank is valid
// -> r int : rank as int ( can be negative )
// <- bool : true = rank is ok, false = rank out of range

func RankOk(r int) bool {
	return (r>=0) && (r<BOARD_HEIGHT)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FileRankOk : file and rank are valid
// -> f int : file as int ( can be negative )
// -> r int : rank as int ( can be negative )
// <- bool : true = file and rank are ok, false = file and rank are not both ok

func FileRankOk(f int, r int) bool {
	return FileOk(f) && RankOk(r)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AlgebFileToFile : file described by algeb letter
// -> af byte : algeb letter of file
// <- TFile : file, 0 if invalid
// <- bool : true = file valid, false = file invalid

func AlgebFileToFile(af byte) (TFile, bool) {
	if (af<'a') || (af>('a'+BOARD_WIDTHL)) {
		return 0, false
	}
	return TFile(af-'a'), true
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FileToAlgebFile : determine algeb letter of file
// -> f TFile : file
// <- byte : algeb letter of file

func FileToAlgebFile(f TFile) byte {
	return byte('a'+byte(f))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AlgebRankToRank : rank described by algeb letter
// -> ar byte : algeb letter of rank
// <- TRank : rank, 0 if invalid
// <- bool : true = rank valid, false = rank invalid

func AlgebRankToRank(ar byte) (TRank, bool) {
	if (ar<'1') || (ar>('1'+BOARD_HEIGHTL)) {
		return 0, false
	}
	return TRank(BOARD_HEIGHTL-(byte(ar)-'1')), true
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// RankToAlgebRank : determine algeb letter of rank
// -> r TRank : rank
// <- byte : algeb letter of rank

func RankToAlgebRank(r TRank) byte {
	return byte('1'+(BOARD_HEIGHTL-byte(r)))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FromFileRank : create a square from file and rank
// -> f TFile : file
// -> r TRank : rank
// <- TSquare : created square

func FromFileRank(f TFile, r TRank) TSquare {
	return TSquare(byte(f)|(byte(r)<<BOARD_SHIFT))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// FromAlgeb : create a square from algeb description
// -> algeb string : algeb description of square
// <- TSquare : created square

func FromAlgeb(algeb string) TSquare {
	if len(algeb)<2 {
		return NO_SQUARE
	}
	f,ok:=AlgebFileToFile(algeb[0])
	if(!ok) {
		return NO_SQUARE
	}
	r,ok:=AlgebRankToRank(algeb[1])
	if(!ok) {
		return NO_SQUARE
	}
	return FromFileRank(f,r)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToAlgeb : determine algeb description of square
// -> sq TSquare : square
// <- string : algeb description of square

func (sq TSquare) ToAlgeb() string {
	if (sq<0) || (sq>BOARD_SIZEL) {
		return "-"
	}
	return fmt.Sprintf("%c%c",FileToAlgebFile(sq.File()),RankToAlgebRank(sq.Rank()))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end square functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// board and move generation functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// CollectAlphaBetaPv : collect alphabeta pv for board position
// -> b TBoard : board
// <- string : pv

func (b TBoard) CollectAlphaBetaPv(max_depth int) string {
	dummy:=b
	buff:=""
	for depth:=0; depth<max_depth; depth++ {
		move,found:=BestMoves[dummy.Pos]
		if !found {
			return buff
		}
		if buff!="" {
			buff=buff+" "
		}
		buff+=move.ToAlgeb()
		dummy.MakeMove(move)
	}
	return buff
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// TerminalEval : evaluation of a board position without legal moves
// -> b TBoard : board
// <- int : eval

func (b TBoard) TerminalEval() int {
	wb:=b.WhiteKingOnBaseRank()
	bb:=b.BlackKingOnBaseRank()

	if wb && bb {
		// both kings on base rank is draw
		return DRAW_SCORE
	}

	if bb {
		// if black king is on base rank it is white's turn
		return -MATE_SCORE
	}

	if wb {
		// if white king is on base rank it is black's turn
		return -MATE_SCORE
	}

	// no king on base rank without legal moves is stalemate
	return DRAW_SCORE
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AlphaBetaRecursive : recursive alphabeta evaluation of the board position to a given max_depth
// -> b TBoard : board
// -> storei int : index to store root eval
// -> depth int : current depth
// -> max_depth int : max depth
// -> alpha int : alpha
// -> beta int : beta
// <- int : eval

func AlphaBetaRecursive(b TBoard,storei int,depth int, max_depth int, alpha int, beta int) int {
	if AbortSearch {
		return INVALID_SCORE
	}
	// SearchNodes is global, needs lock
	mutex.Lock()
	SearchNodes++
	mutex.Unlock()
	b.InitMoveGen()
	haslegal:=b.NextLegalMove()
	if !haslegal {
		eval:=b.TerminalEval()
		realdepth:=depth+b.BaseDepth
		if eval<0 {
			eval+=realdepth
		} else {
			eval-=realdepth
		}
		if depth==0 {
			AlphaBetaEvals[storei]=eval
		}
		return eval
	}
	if depth>=max_depth {
		eval:=b.Eval()
		if depth==0 {
			AlphaBetaEvals[storei]=eval
		}
		return eval
	}
	currentbest:=-INFINITE_SCORE
	//ml:=b.CreateMoveList()
	//mi:=0
	for haslegal {
		m:=b.CurrentMove
		//m:=ml[mi]

		effectivebeta:=beta
		if depth==0 {
			effectivebeta=-BaseAlpha
		}

		var round=1
		if (max_depth>=PruneFromDepth)&&(depth>=PruneThresoldLow)&&(depth<=PruneThresoldHigh) {
			round=0
		}
		if MateSearch {
			round=1
		}
		for ;round<2;round++ {
			b.MakeMove(m)
			eff_depth:=max_depth
			if round==0 {
				eff_depth=depth+PruneDepth
				if(eff_depth>max_depth){
					eff_depth=max_depth
				}
			}
			eval:=-AlphaBetaRecursive(b,-1,depth+1,eff_depth,-beta,-alpha)
			b.UnMakeMove(m)
			if round==1 {
				// test whether this is new best move
				if eval>currentbest {
					// new best move found
					// make this eval the current best
					currentbest=eval
					// set move's eval
					m.Eval=eval
					// store as best move
					// multithreaded, so setting common resource BestMoves requires lock
					mutex.Lock()
					BestMoves[b.Pos]=m
					mutex.Unlock()
				}
				// update alpha
				if eval>alpha {
					alpha=eval
				}
			}
			// test whether it is a cut
			if eval>effectivebeta {
				// cut
				if depth==0 {
					AlphaBetaEvals[storei]=eval
				}
				if round==0 {
					m.Eval=eval
					// store as best move
					// multithreaded, so setting common resource BestMoves requires lock
					mutex.Lock()
					BestMoves[b.Pos]=m
					mutex.Unlock()
				}
				return eval
			}
		}

		haslegal=b.NextLegalMove()
		//mi++
		//haslegal=mi<len(ml)
	}
	if depth==0 {
		AlphaBetaEvals[storei]=alpha
	}
	return alpha
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AlphaBeta : alphabeta evaluation of the board position to a given max_depth
// -> b *TBoard : board
// -> max_depth int : maximum depth of search
// <- int : eval

func (b TBoard) AlphaBeta(max_depth int) int {
	// get node for board
	node:=b.Node()
	// determine number of legal moves
	l:=len(node.Moves)
	NumAlphaBetaMoves=l
	// if none, return terminal eval
	if l<=0 {
		return b.TerminalEval()
	}
	// start with INVALID_SCORE for all moves to signal that evaluation has not arrived yet
	for i:=0; i<=l; i++ {
		AlphaBetaEvals[i]=INVALID_SCORE
	}
	// base for current chunk of moves
	BaseAlpha=-INFINITE_SCORE
	basei:=0
	for basei<l {
		// determine last index of chunk
		lasti:=basei+NumThreads-1
		if lasti>=l {
			lasti=l-1
		}
		// increase base depth of board
		b.BaseDepth++
		// make moves one by one in the chunk and start alphabetarecursive in separate thread for each resulting position
		for i:=basei; i<=lasti; i++ {
			m:=node.Moves[i]
			b.MakeMove(m)
			go AlphaBetaRecursive(b,i,0, max_depth-1, -INFINITE_SCORE, -BaseAlpha)
			b.UnMakeMove(m)
		}
		// restore base depth of board
		b.BaseDepth--
		// wait for all chunk evals to arrive or abort
		ready:=false
		for (!ready) && (!AbortSearch) {
			ready=true
			for i:=basei; i<=lasti; i++ {
				eval:=-AlphaBetaEvals[i]
				if eval==-INVALID_SCORE {
					ready=false
				} else {
					// update BaseAlpha
					if eval>BaseAlpha {
						BaseAlpha=eval
					}
				}
			}
			if !ready {
				time.Sleep(20 * time.Millisecond)
			}
		}
		// if aborted return invalid score
		if AbortSearch {
			return INVALID_SCORE
		}
		// store returned chunk evals in the node
		for i:=basei; i<=lasti; i++ {
			eval:=-AlphaBetaEvals[i]
			// update BaseAlpha
			if eval>BaseAlpha {
				BaseAlpha=eval
			}
			node.Moves[i].Eval=eval
		}
		// to to next chunk
		basei+=NumThreads
	}
	// sort the node
	node.Sort()
	// determine alpha, bestmove algeb and store evals and moves in the appropriate global variables
	alpha:=-INFINITE_SCORE
	for i:=0; i<l; i++ {
		m:=node.Moves[i]
		eval:=m.Eval
		if eval>alpha {
			alpha=eval
			BestMoveAlgeb=m.ToAlgeb()
		}
		AlphaBetaEvals[i]=eval
		AlphaBetaMoves[i]=m
	}
	// store the sorted node in cache
	Nodes[b.Pos]=node
	// return alpha
	return alpha
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// EvalNode : evaluate moves in the node belonging to board pos at depth and store in cache
// -> b TBoard : board
// -> depth int : depth
// <- TNode : the evaluated node

func (b TBoard) EvalNode(depth int) TNode {
	b.AlphaBeta(depth)
	return b.Node()
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CreateNode : creates a node for a given board
// -> b TBoard : board
// <- TNode : created node

func (b TBoard) CreateNode() TNode {
	n:=TNode{}
	n.Moves=b.CreateMoveList()
	return n
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Node : get the node belonging to the board from cache or create one and store it cache
// -> b TBoard : board
// <- TNode : node

func (b TBoard) Node() TNode {
	if DoesNodeExist(b.Pos) {
		return Nodes[b.Pos]
	}
	n:=b.CreateNode()
	Nodes[b.Pos]=n
	return n
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// EvalCol : heuristic eval the board position for color
// -> b TBoard : board
// -> c TColor : color
// <- int : eval

func (b TBoard) EvalCol(c TColor) int {
	eval:=b.Material[IndexOfColor(c)]
	ksq:=b.KingPositions[IndexOfColor(c)]
	ksqr:=int(BOARD_HEIGHTL-ksq.Rank())
	eval+=ksqr*KING_ADVANCE_VALUE
	return eval
}

///////////////////////////////////////////////

var mutex = &sync.Mutex{}

///////////////////////////////////////////////
// Eval : heuristic eval of the board position
// -> b TBoard : board
// <- int : eval

func (b TBoard) Eval() int {
	// calculate eval from white's viewpoint by subtracting black's value from white's value
	eval:=b.EvalCol(WHITE)-b.EvalCol(BLACK)
	// generate random number in the -100 .. +100 range
	mutex.Lock() // has to lock because random number generator is not thread safe
	r:=Rand.Intn(2*Randomness+1)-Randomness
	mutex.Unlock()
	// add some fraction of random number to eval
	// the goal is to generate more cuts
	// the correct value is determined by trial and error
	// in the starting position dividing by 10 seems best
	eval+=r
	// if white's turn return eval
	if b.Pos.Turn==WHITE {
		return eval
	}
	// if black's turn return -eval, to reflect the evaluation from black's viewpoint
	return -eval
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToAlgeb : move to algeb
// -> m TMove : move
// <- string : algeb

func (m TMove) ToAlgeb() string {
	return fmt.Sprintf("%s%s",m.From.ToAlgeb(),m.To.ToAlgeb())
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// GetMoveTablePtr : move table pointer for square and piece
// -> sq TSquare : square
// -> p TPiece : piece
// <- int : move table pointer

func GetMoveTablePtr(sq TSquare, p TPiece) int {
	return MoveTablePtrs[TMoveTableKey{sq,p}]
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// NextSq : next square in move generation
// -> b *TBoard : board
// <- bool : true = square found, false = no more squares for move generation

func (b *TBoard) NextSq() bool {
	for b.CurrentSq<BOARD_SIZE {
		p:=b.PieceAtSq(b.CurrentSq)
		if p.Color()==b.Pos.Turn {
			b.CurrentPiece=p
			b.CurrentPtr=GetMoveTablePtr(b.CurrentSq,b.CurrentPiece)
			return true
		}
		b.CurrentSq++
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// InitMoveGen : init move generator
// -> b *TBoard : board

func (b *TBoard) InitMoveGen() {
	b.CurrentSq=0
	b.NextSq()
	b.HasBestMove=false
	b.BestMoveDone=true
	bestmove,found:=BestMoves[b.Pos]
	if found {
		b.BestMoveDone=false
		b.HasBestMove=true
		b.BestMove=bestmove
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// NextPseudoLegalMove : next pseudo legal move in move generation
// -> b *TBoard : board
// <- bool : true = legal move found, false = no more legal moves

func (b *TBoard) NextPseudoLegalMove() bool {
	for b.CurrentSq<BOARD_SIZE {
		md:=MoveTable[b.CurrentPtr]
		if md.EndPiece {
			b.CurrentSq++
			b.NextSq()
		} else {
			cp:=b.PieceAtSq(md.To)
			c:=cp.Color()
			if c==b.Pos.Turn {
				// own piece
				b.CurrentPtr=md.NextVector
			} else if c==NO_COLOR {
				// empty
				b.CurrentMove=TMove{b.CurrentSq,md.To,b.CurrentPiece,cp,0,false,false}
				b.CurrentPtr++
				return true
			} else {
				// capture
				b.CurrentMove=TMove{b.CurrentSq,md.To,b.CurrentPiece,cp,0,false,false}
				b.CurrentPtr=md.NextVector
				return true
			}
		}
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// KingOnBaseRank : is king of given color on base rank
// -> b TBoard : board
// -> c TColor : color
// <- bool : true = king is on base rank, false = king is not on base rank

func (b TBoard) KingOnBaseRank(c TColor) bool {
	return (b.KingPositions[IndexOfColor(c)].Rank()==0)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// WhiteKingOnBaseRank : white king on base rank
// -> b TBoard : board
// <- bool : true = white king is on base rank, false = white king is not on base rank

func (b TBoard) WhiteKingOnBaseRank() bool {
	return b.KingOnBaseRank(WHITE)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// BlackKingOnBaseRank : black king on base rank
// -> b TBoard : board
// <- bool : true = black king is on base rank, false = black king is not on base rank

func (b TBoard) BlackKingOnBaseRank() bool {
	return b.KingOnBaseRank(BLACK)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsWhiteTurn : is it white's turn
// -> b TBoard : 
// <- bool : true = it is white's turn, false = it is not white's turn

func (b TBoard) IsWhiteTurn() bool {
	return (b.Pos.Turn==WHITE)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsBlackTurn : is it black's turn
// -> b TBoard : 
// <- bool : true = it is black's turn, false = it is not black's turn

func (b TBoard) IsBlackTurn() bool {
	return (b.Pos.Turn==BLACK)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// SetSq : place a piece on a square
// -> b *TBoard : board
// -> sq *TSquare : square
// -> p *TPiece : piece

func (b *TBoard) SetSq(sq TSquare,p TPiece) {
	b.Pos.Rep[byte(sq)]=byte(p)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// MakeMove : make a move on board
// -> b *TBoard : board
// -> m TMove : move

func (b *TBoard) MakeMove(m TMove) {

	b.SetSq(m.From,NO_PIECE)

	b.SetSq(m.To,m.Piece)

	if(m.Piece==(WHITE|KING)) {
		b.KingPositions[INDEX_OF_WHITE]=m.To
	}

	if(m.Piece==(BLACK|KING)) {
		b.KingPositions[INDEX_OF_BLACK]=m.To
	}

	b.Material[IndexOfColor(InvColorOf(b.Pos.Turn))]-=PIECE_VALUES[m.CapPiece.Type()]

	b.Pos.Depth=b.Pos.Depth+1

	b.Pos.Turn=InvColorOf(b.Pos.Turn)

}

///////////////////////////////////////////////

///////////////////////////////////////////////
// UnMakeMove : unmake move on board
// -> b *TBoard : board
// -> m TMove : move

func (b *TBoard) UnMakeMove(m TMove) {

	b.SetSq(m.From,m.Piece)

	if(m.Piece==(WHITE|KING)) {
		b.KingPositions[INDEX_OF_WHITE]=m.From
	}

	if(m.Piece==(BLACK|KING)) {
		b.KingPositions[INDEX_OF_BLACK]=m.From
	}

	b.SetSq(m.To,m.CapPiece)

	b.Material[IndexOfColor(b.Pos.Turn)]+=PIECE_VALUES[m.CapPiece.Type()]

	b.Pos.Depth=b.Pos.Depth-1

	b.Pos.Turn=InvColorOf(b.Pos.Turn)

}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsSquareColInCheck : is color in check at some square
// -> sq TSquare : square
// -> c TColor : color
// <- bool : true = in check, false = not in check

func (b TBoard) IsSquareColInCheck(sq TSquare, c TColor) bool {
	ksq:=b.KingPositions[IndexOfColor(c)]
	for _, pt := range ALL_PIECE_TYPES {
		test_piece:=FromTypeAndColor(pt,InvColorOf(c))
		ptr:=GetMoveTablePtr(ksq,test_piece)
		for !MoveTable[ptr].EndPiece {
			md:=MoveTable[ptr]
			p:=b.PieceAtSq(md.To)
			if p==test_piece {
				return true
			}
			if p.Color()!=NO_COLOR {
				ptr=md.NextVector
			} else {
				ptr++
			}
		}
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsSqInCheck : is turn in check at square
// -> b TBoard : board
// <-  : 

func (b TBoard) IsSqInCheck(sq TSquare) bool {
	return b.IsSquareColInCheck(sq,b.Pos.Turn)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsColInCheck : is color in check
// -> b TBoard : board
// <- bool : true = is in check, false = not in check

func (b TBoard) IsColInCheck(c TColor) bool {
	return b.IsSquareColInCheck(b.KingPositions[IndexOfColor(c)],c)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsInCheck : is turn in check
// -> b TBoard : board
// <- bool : true = is in check, false = not in check

func (b TBoard) IsInCheck() bool {
	return b.IsColInCheck(b.Pos.Turn)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsOppInCheck : is inverse turn in check
// -> b TBoard : board
// <- bool : true = is in check, false = not in check

func (b TBoard) IsOppInCheck() bool {
	return b.IsColInCheck(InvColorOf(b.Pos.Turn))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// NextLegalMove : next legal move in move generation
// -> b *TBoard : board
// <- bool : true = legal move found, false = no more legal moves

func (b *TBoard) NextLegalMove() bool {
	if b.BlackKingOnBaseRank() {
		return false
	}
	wb:=b.WhiteKingOnBaseRank()
	if wb && b.IsWhiteTurn() {
		return false
	}
	if b.HasBestMove {
		if !b.BestMoveDone {
			b.CurrentMove=b.BestMove
			b.CurrentMove.IsAlphaBetaBestMove=true
			b.BestMoveDone=true
			return true
		}
	}
	for b.NextPseudoLegalMove() {
		b.MakeMove(b.CurrentMove)
		incheck:=b.IsInCheck()
		oppincheck:=b.IsOppInCheck()
		blackmated:=(wb && (!b.BlackKingOnBaseRank()))
		b.UnMakeMove(b.CurrentMove)
		ok:=(!incheck)&&(!oppincheck)&&(!blackmated)
		if ok {
			if b.BestMoveDone || (b.CurrentMove!=b.BestMove) {
				// move is ok
				if b.CurrentMove.Piece.Type()==KING {
					if b.CurrentMove.To.Rank()<b.CurrentMove.From.Rank() {
						b.CurrentMove.IsForwardKingMove=true
					}
				}
				return true
			}
		}
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IndexOfColor : index of color from 0 to 1
// -> c TColor : color
// <- int : index, 0 = BLACK, 1 = WHITE

func IndexOfColor(c TColor) int {
	return int(byte(c)>>1)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// PieceAtSq : piece at square
// -> b TBoard : board
// <- TPiece : piece

func (b TBoard) PieceAtSq(sq TSquare) TPiece {
	return TPiece(b.Pos.Rep[byte(sq)])
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CalcMaterial : calculate material
// -> b TBoard : board
// <-  : 

func (b *TBoard) CalcMaterial() {
	b.Material[INDEX_OF_WHITE]=0
	b.Material[INDEX_OF_BLACK]=0
	for sq:=0; sq<BOARD_SIZE; sq++ {
		p:=b.PieceAtSq(TSquare(sq))
		c:=p.Color()
		t:=p.Type()
		b.Material[IndexOfColor(c)]+=PIECE_VALUES[t]
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// SetFromFen : set the board from fen
// -> b *TBoard : board
// -> fen string : fen
// <- bool : true = success, false = failed

///////////////////////////////////////////////

func (b *TBoard) SetFromFen(fen string) bool {
	var l=len(fen)

	if l<=0 {
		return false
	}

	var ok=true

	var ptr=0

	var feni=0

	for ; (feni<l) && ok ; feni++ {
		c:=fen[feni]

		if (c>='1') && (c<='8') {
			for fill:=0; fill<int(c-'0'); fill++ {
				if(ptr<BOARD_SIZE) {
					b.Pos.Rep[ptr]=NO_PIECE
					ptr++
				}
			}
		} else if(ptr<BOARD_SIZE) {
			p:=FromFenChar(c)
			if p!=NO_PIECE {
				b.Pos.Rep[ptr]=byte(p)
				if p.Type()==KING {
					b.KingPositions[IndexOfColor(p.Color())]=TSquare(ptr)
				}
				ptr++
			}
		}

		ok=(ptr<BOARD_SIZE)
	}

	if (ptr<BOARD_SIZE) || (feni>=(l-1)) {
		return false
	}

	b.Pos.Turn=WHITE

	feni++

	if fen[feni]=='b' {
		b.Pos.Turn=BLACK
	}

	b.Pos.Depth=0
	b.BaseDepth=0

	b.CalcMaterial()

	return true
}

///////////////////////////////////////////////
// TurnToChar : determine turn fen letter of turn w/b
// -> t TColor : turn
// <- byte : turn fen letter

func TurnToChar(t TColor) byte {
	if t==BLACK {
		return 'b'
	}
	return 'w'
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToPrintable : 
// -> b TBoard : board
// <- string : printable form of board

func (b TBoard) ToPrintable() string {
	var buff=""

	for i:=0; i<BOARD_SIZE; i++ {
		var fenchar=ToFenChar(TPiece(b.Pos.Rep[i]))
		if fenchar==' ' {
			fenchar='.'
		}
		buff+=string(fenchar)
		if ((i+1) % BOARD_WIDTH)==0 {
			switch ((i+1)/BOARD_WIDTH-1) {
				case 0 : buff+=fmt.Sprintf(" turn %c\n",TurnToChar(b.Pos.Turn))
				case 1 : buff+=fmt.Sprintf(" depth %d\n",b.Pos.Depth)
				case 2 : buff+=fmt.Sprintf(" white king pos %s\n",b.KingPositions[INDEX_OF_WHITE].ToAlgeb())
				case 3 : buff+=fmt.Sprintf(" black king pos %s\n",b.KingPositions[INDEX_OF_BLACK].ToAlgeb())
				case 4 : buff+=fmt.Sprintf(" eval white %d\n",b.EvalCol(WHITE))
				case 5 : buff+=fmt.Sprintf(" eval black %d\n",b.EvalCol(BLACK))
				case 6 : buff+=fmt.Sprintf(" eval %d\n",b.Eval())
				default: buff+="\n"
			}
		}
	}

	return buff
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end board and move generation functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// IsBool : determine if Token can be parsed as bool and is so parse it and store it in global variable B
// <- bool : true = Token parsed as bool ok, false = Token cannot be parsed as bool

func IsBool() bool {
	lToken:=strings.ToLower(Token)
	if lToken=="true" {
		B=true
		return true
	}
	if lToken=="false" {
		B=false
		return true
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// IsInt : determine if Token can be parsed as an int and is so parse it and store it in global variable I
// <- bool : true = Token parsed as int ok, false = Token cannot be parsed as int

func IsInt() bool {
	i,err:=strconv.Atoi(Token)
	if err==nil {
		I=i
		return true
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// NextToken : reads the next token from scanner
// <- bool : true = read successful, global var Token contains the token
//         : false = read failed, global var Token is set to ""

func NextToken() bool {
	if Scanner.Scan()!=scanner.EOF {
		Token=Scanner.TokenText()
		return true
	} else {
		Token=""
		return false
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Printu : unbuffered write to stdout
// -> ucistr string : string to be written

func Printu(ucistr string) {
	os.Stdout.Write([]byte(ucistr))
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Log : append string to log.txt
// -> what string : string to be appended

func Log(what string) {
	f,err:=os.OpenFile("log.txt",os.O_CREATE|os.O_APPEND|os.O_WRONLY,0666)
	if err!=nil {
	    panic(err)
	}

	defer f.Close()

	if _,err=f.WriteString(what); err!=nil {
	    panic(err)
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ClearLog : create an empty log.txt file

func ClearLog() {
f,err:=os.Create("log.txt")
	if err!=nil {
		panic(err)
	} else {
		f.Close()
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ClearBestMoves : clear alphabeta best moves

func ClearBestMoves() {
	BestMoves=make(map[TPosition]TMove)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ClearNodes : clear nodes

func ClearNodes() {
	Nodes=make(map[TPosition]TNode)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ClearHash : clear hash

func ClearHash() {
	ClearBestMoves()
	ClearNodes()
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CalcTimeNps : calc time and nodes per second

func CalcTimeNps() {
	CurrentTime := time.Now().UTC()
	Time=CurrentTime.Sub(StartingTime).Nanoseconds()/1e6
	Nps=int64(0)
	if(Time>0) {
		Nps=int64(SearchNodes)*1e3/Time
	}
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CalcScore : determine uci score of Eval and store it in Score

func CalcScore() {
	if (Eval>(-MATE_LIMIT)) && (Eval<MATE_LIMIT) {
		Score=fmt.Sprintf("score cp %d",Eval)
		return
	}
	if Eval>0 {
		Score=fmt.Sprintf("score mate %d",MATE_SCORE-Eval)
		return
	}
	Score=fmt.Sprintf("score mate -%d",Eval+MATE_SCORE)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// UciInfo : determine uci info string
// <- string : uci infor string

func UciInfo() string {
	CalcTimeNps()
	CalcScore()
	return fmt.Sprintf("info time %d depth %d multipv %d nodes %d nps %d %s pv %s",
		Time,Depth,MultiPVIndex,SearchNodes,Nps,Score,Pv)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// SendBestMove : send best move

func SendBestMove() {
	Printu("bestmove "+BestMoveAlgeb+"\n")
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// SendUciInfo : calculate and send uci info

func SendUciInfo() {
	Printu(UciInfo()+"\n")
	Log(UciInfo()+"\n")
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// StartTimer : start timer

func StartTimer() {
	StartingTime=time.Now().UTC()
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// InterpretTestCommand : interpret test Command read from commandline

func InterpretTestCommand() {

	if Command=="x" {
		Command="quit"
		return
	}

	if Command=="s" {
		Command="stop"
		return
	}

	if Command=="r" {
		G.SetFromFen(START_FEN)
		G.Print()
	}

	if Command=="c" {
		ClearBestMoves()
	}

	if Command=="a" {
		AbortSearch=false
		SearchDepth=MAX_SEARCH_DEPTH

		go G.RandomSearch()
	}

	if Command=="e" {
		depth:=1
		if NextToken() && IsInt() {
			depth=I
		}
		G.B.EvalNode(depth)
		G.Print()
	}

	if Command=="n" {
		NumThreads=MAX_MULTIPV
		if NextToken() && IsInt() {
			NumThreads=I
		}
	}

	if Command=="d" {
		G.DelMove()
		G.Print()
	}

	if Command=="p" {
		G.Print()
	}

	if Command=="m" {
		if NextToken() {
			G.MakeAlgebMove(Token)
			G.Print()
		}
	}

}

///////////////////////////////////////////////

///////////////////////////////////////////////
// InterpretCommand : interpret Command read from commandline

func InterpretCommand() {

/* from "Description of the universal chess interface (UCI)    April  2006":
uci
	tell engine to use the uci (universal chess interface),
	this will be sent once as a first command after program boot
	to tell the engine to switch to uci mode.
	After receiving the uci command the engine must identify itself with the "id" command
	and send the "option" commands to tell the GUI which engine settings the engine supports if any.
	After that the engine should send "uciok" to acknowledge the uci mode.
	If no uciok is sent within a certain time period, the engine task will be killed by the GUI.
*/
	
	if(Command=="uci") {
		Printu(RESPONSE_TO_UCI_COMMAND)
	}

/* from "Description of the universal chess interface (UCI)    April  2006":
isready
	this is used to synchronize the engine with the GUI. When the GUI has sent a command or
	multiple commands that can take some time to complete,
	this command can be used to wait for the engine to be ready again or
	to ping the engine to find out if it is still alive.
	E.g. this should be sent after setting the path to the tablebases as this can take some time.
	This command is also required once before the engine is asked to do any search
	to wait for the engine to finish initializing.
	This command must always be answered with "readyok" and can be sent also when the engine is calculating
	in which case the engine should also immediately answer with "readyok" without stopping the search.
*/

	if Command=="isready" {
		Printu("readyok\n")
	}

/* from "Description of the universal chess interface (UCI)    April  2006":
setoption name <id> [value <x>]
	this is sent to the engine when the user wants to change the internal parameters
	of the engine. For the "button" type no value is needed.
	One string will be sent for each parameter and this will only be sent when the engine is waiting.
	The name and value of the option in <id> should not be case sensitive and can inlude spaces.
	The substrings "value" and "name" should be avoided in <id> and <x> to allow unambiguous parsing,
	for example do not use <name> = "draw value".
	Here are some strings for the example below:
	   "setoption name Nullmove value true\n"
      "setoption name Selectivity value 3\n"
	   "setoption name Style value Risky\n"
	   "setoption name Clear Hash\n"
	   "setoption name NalimovPath value c:\chess\tb\4;c:\chess\tb\5\n"
*/

	if Command=="setoption" {
		if NextToken() {
			if(Token=="name") {
				if NextToken() {
					name:=Token
					if name=="ClearHash" {
						ClearHash()
						return
					}
					if NextToken() {
						if(Token=="value") {
							if NextToken() {
								if name=="MultiPV" {
									if IsInt() {
										MultiPV=I
									}
								}
								if name=="MateSearch" {
									if IsBool() {
										MateSearch=B
									}
								}
								if name=="RandomSearch" {
									if IsBool() {
										RandomSearch=B
									}
								}
								if name=="Randomness" {
									if IsInt() {
										Randomness=I
									}
								}
								if name=="Branching" {
									if IsInt() {
										Branching=I
									}
								}
								if name=="KingAdvanceValue" {
									if IsInt() {
										KING_ADVANCE_VALUE=I
									}
								}
								if name=="KnightValue" {
									if IsInt() {
										PIECE_VALUES[KNIGHT]=I
									}
								}
								if name=="BishopValue" {
									if IsInt() {
										PIECE_VALUES[BISHOP]=I
									}
								}
								if name=="RookValue" {
									if IsInt() {
										PIECE_VALUES[ROOK]=I
									}
								}
								if name=="QueenValue" {
									if IsInt() {
										PIECE_VALUES[QUEEN]=I
									}
								}
								if name=="RandomDepthOdd" {
									if IsInt() {
										RandomDepthOdd=I
									}
								}
								if name=="RandomDepthEven" {
									if IsInt() {
										RandomDepthEven=I
									}
								}
								if name=="PruneThresoldLow" {
									if IsInt() {
										PruneThresoldLow=I
									}
								}
								if name=="PruneThresoldHigh" {
									if IsInt() {
										PruneThresoldHigh=I
									}
								}
								if name=="PruneFromDepth" {
									if IsInt() {
										PruneFromDepth=I
									}
								}
								if name=="PruneDepth" {
									if IsInt() {
										PruneDepth=I
									}
								}
							}
						}
					}
				}
			}
		}
	}

/* from "Description of the universal chess interface (UCI)    April  2006":
position [fen <fenstring> | startpos ]  moves <move1> .... <movei>
	set up the position described in fenstring on the internal board and
	play the moves on the internal chess board.
	if the game was played  from the start position the string "startpos" will be sent
	Note: no "new" command is needed. However, if this position is from a different game than
	the last position sent to the engine, the GUI should have sent a "ucinewgame" inbetween.
*/

	if Command=="position" {
		// 0 - position
		// 1 - startpos
		// 2 - moves
		// 3 - move1
		// 4 - move2
		// 5 - ...

		// or...

		// 0 - position
		// 1 - fen
		// 2 - posfen
		// 3 - turnfen
		// 4 - castlefen
		// 5 - epfen
		// 6 - halfmovefen
		// 7 - fullmovefen
		// 8 - moves
		// 9 - move1
		// 10 - move2
		// 11 - ...

		if NextToken() {
			fen:=START_FEN
			movesat:=2
			parts:=strings.Split(Commandline," ")
			if(Token=="fen") {
				if NextToken() {
					if len(parts)>=8 {
						fen=fmt.Sprintf("%s %s %s %s %s %s",parts[2],parts[3],parts[4],parts[5],parts[6],parts[7])
						movesat=8
					}
				}
			}
			G.SetFromFen(fen)
			if len(parts)>movesat {
				if parts[movesat]=="moves" {
					for i:=movesat+1; i<len(parts); i++ {
						G.MakeAlgebMove(parts[i])
					}
				}
			}
		}
	}

/* from "Description of the universal chess interface (UCI)    April  2006":
go
	start calculating on the current position set up with the "position" command.
	There are a number of commands that can follow this command, all will be sent in the same string.
	If one command is not sent its value should be interpreted as it would not influence the search.
	* searchmoves <move1> .... <movei>
		restrict search to this moves only
		Example: After "position startpos" and "go infinite searchmoves e2e4 d2d4"
		the engine should only search the two moves e2e4 and d2d4 in the initial position.
	* ponder
		start searching in pondering mode.
		Do not exit the search in ponder mode, even if it's mate!
		This means that the last move sent in in the position string is the ponder move.
		The engine can do what it wants to do, but after a "ponderhit" command
		it should execute the suggested move to ponder on. This means that the ponder move sent by
		the GUI can be interpreted as a recommendation about which move to ponder. However, if the
		engine decides to ponder on a different move, it should not display any mainlines as they are
		likely to be misinterpreted by the GUI because the GUI expects the engine to ponder
	   on the suggested move.
	* wtime <x>
		white has x msec left on the clock
	* btime <x>
		black has x msec left on the clock
	* winc <x>
		white increment per move in mseconds if x > 0
	* binc <x>
		black increment per move in mseconds if x > 0
	* movestogo <x>
      there are x moves to the next time control,
		this will only be sent if x > 0,
		if you don't get this and get the wtime and btime it's sudden death
	* depth <x>
		search x plies only.
	* nodes <x>
	   search x nodes only,
	* mate <x>
		search for a mate in x moves
	* movetime <x>
		search exactly x mseconds
	* infinite
		search until the "stop" command. Do not exit the search without being told so in this mode!
*/

	if Command=="go" {
		AbortSearch=false	
		SearchDepth=MAX_SEARCH_DEPTH

		for NextToken() {
			if Token=="depth" {
				if NextToken() && IsInt() {
					SearchDepth=I
				}
			}
		}

		if RandomSearch {
			go G.RandomSearch()
		} else {
			go G.AlphaBetaSearch()
		}
	}

/* from "Description of the universal chess interface (UCI)    April  2006":
stop
	stop calculating as soon as possible,
	don't forget the "bestmove" and possibly the "ponder" token when finishing the search
*/

	if Command=="stop" {
		AbortSearch=true

		for !SearchReady {
			time.Sleep(50 * time.Millisecond)
		}
	}

}

///////////////////////////////////////////////

///////////////////////////////////////////////
// movelist functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// Sort : sort movelist for the purposes of move ordering
// -> ml *TMoveList : move list

func (ml *TMoveList) Sort() {
	sort.Sort(ml)
}

func (ml *TMoveList) Len() int {
	return len(*ml)
}

func (ml *TMoveList) Less(i,j int) bool {
	if (*ml)[i].IsAlphaBetaBestMove {
		return true
	}
	evalcomp:=(*ml)[i].Eval>(*ml)[j].Eval
	if (*ml)[i].IsForwardKingMove && (*ml)[j].IsForwardKingMove {
		return evalcomp
	}
	if (*ml)[i].IsForwardKingMove {
		return true
	}
	if ((*ml)[i].CapPiece!=NO_PIECE) && ((*ml)[j].CapPiece!=NO_PIECE) {
			return evalcomp
	}
	if ((*ml)[i].CapPiece!=NO_PIECE) {
		return true
	}
	return evalcomp
}

func (ml *TMoveList) Swap(i,j int) {
	(*ml)[i] , (*ml)[j] = (*ml)[j] , (*ml)[i]
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CreateMoveList : creates movelist for a given board
// -> b TBoard : board
// <- TMoveList : created move list

func (b TBoard) CreateMoveList() TMoveList {
	ml:=TMoveList{}
	b.InitMoveGen()
	for b.NextLegalMove() {
		m:=b.CurrentMove
		m.Eval=INVALID_SCORE
		ml=append(ml,m)
	}
	return ml
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToPrintable : create printable version of move list
// -> ml TMoveList : move list
// <- string : printable version of move list

func (ml TMoveList) ToPrintable() string {
	if len(ml)==0 {
		return "*"
	}
	buff:=""
	for i,m := range ml {
		buff=buff+m.ToAlgeb()
		if i<(len(ml)-1) {
			buff=buff+" "
		}
	}
	return buff
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end movelist functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// game functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// MinimaxOutRecursive : mimimax out recursive
// -> g *TGame : game
// -> b TBoard : board belonging to current position
// -> depth int : depth
// -> max_depth int : max depth
// <- int : eval

func (g *TGame) MinimaxOutRecursive(b TBoard, depth int, max_depth int) int {
	if AbortSearch {
		return INVALID_SCORE
	}
	if !DoesNodeExist(b.Pos) {
		return INVALID_SCORE
	}
	if depth>max_depth {
		return INVALID_SCORE
	}
	node:=b.Node()
	l:=len(node.Moves)
	if l<=0 {
		return b.TerminalEval()
	}
	alpha:=-INFINITE_SCORE
	for i,m := range node.Moves {
		b.MakeMove(m)
		eval:=-g.MinimaxOutRecursive(b, depth+1, max_depth)
		if eval==-INVALID_SCORE {
			eval=m.Eval
		}
		node.Moves[i].Eval=eval
		if eval>alpha {
			alpha=eval
		}
		b.UnMakeMove(m)
	}
	node.Sort()
	Nodes[b.Pos]=node
	return alpha
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// MinimaxOut : minimax out tree starting from game's board position
// -> g *TGame : game

func (g *TGame) MinimaxOut(max_depth int) {
	g.MinimaxOutRecursive(g.B, 0, max_depth)
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// CollectRandomPv : collect pv from tree starting from game's board position
// -> g *TGame : game
// -> depth int : depth
// <- string : pv

func (g *TGame) CollectRandomPv(depth int) string {
	buff:=""
	dummy:=g.B
	exists:=DoesNodeExist(dummy.Pos)
	for i:=0; exists && (i<depth) && (len(dummy.Node().Moves)>0); i++ {
		m:=dummy.Node().Moves[0]
		if buff!=""	{
			buff+=" "
		}
		buff+=m.ToAlgeb()
		dummy.MakeMove(m)
		exists=DoesNodeExist(dummy.Pos)
	}
	return buff
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AddNodeRecursive : add node recursively
// -> g *TGame : game
// -> b TBoard : board belonging to current node
// -> depth int : depth
// -> max_depth int : max depth
// -> ml TMoveList : line
// <- bool : true = node added ok, false = adding node failed

func (g *TGame) AddNodeRecursive(b TBoard, depth int, max_depth int, ml TMoveList) bool {
	if depth>max_depth {
		return false
	}
	if !DoesNodeExist(b.Pos) {
		if((depth%2)==0){
			b.EvalNode(RandomDepthEven)
		} else {
			b.EvalNode(RandomDepthOdd)
		}
		if TEST {
			//fmt.Printf("added line %s\n",ml.ToPrintable())
		}
		return true
	}
	node:=b.Node()
	l:=len(node.Moves)
	for i:=0; i<l; i++ {
		m:=node.Moves[i]
		moveok:=(i==(l-1))||(Rand.Intn(100)>=Branching)
		if moveok {
			b.MakeMove(m)
			return g.AddNodeRecursive(b, depth+1, max_depth,append(ml,m))
		}
	}
	// should not get here
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AddNode : add random node to tree starting from game's board position
// -> g *TGame : game
// -> max_depth int : max depth
// <- bool : true = node added ok, false = failed to add node

func (g *TGame) AddNode(max_depth int) bool {
	return g.AddNodeRecursive(g.B,0,max_depth,TMoveList{})
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// RandomSearch : perform random search for game's board position
// -> g *TGame : game

func (g *TGame) RandomSearch() {
	node:=g.B.Node()
	if len(node.Moves)<=0 {
		SearchReady=true
		return
	}
	SearchReady=false
	SearchNodes=0
	g.B.BaseDepth=0
	BestMoveAlgeb=""
	Depth=1
	StartTimer()

	g.B.EvalNode(0)

	// add some random nodes to tree
	for (Depth<=SearchDepth) && (!AbortSearch) {
		for k:=0; (k<Depth) && (!AbortSearch); k++ {
			for i:=0; (i<Depth) && (!AbortSearch); i++ {
				g.AddNode(Depth)
			}

			g.MinimaxOut(Depth)

			node:=g.B.Node()
			for i:=0; i<=(MultiPV-1); i++ {
				if i<len(node.Moves) {
					m:=node.Moves[i]
					Pv=m.ToAlgeb()
					g.B.MakeMove(m)
					collectedpv:=g.CollectRandomPv(Depth-1)
					if collectedpv!="" {
						Pv+=" "+collectedpv
					}
					g.B.UnMakeMove(m)
					Eval=m.Eval
					MultiPVIndex=i+1
					SendUciInfo()
				}
			}
		}

		ClearBestMoves()
		Depth++
	}

	BestMoveAlgeb=g.B.Node().Moves[0].ToAlgeb()
	SendBestMove()
	SearchReady=true
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// AlphaBetaSearch : perform alphabeta search for game's board position
// -> g *TGame : game

func (g *TGame) AlphaBetaSearch() {
	SearchReady=false
	SearchNodes=0
	g.B.BaseDepth=0
	BestMoveAlgeb=""
	Depth=1
	StartTimer()

	for (Depth<=SearchDepth) && (!AbortSearch) {
		g.B.AlphaBeta(Depth)
		if !AbortSearch {
			for i:=0; i<=(MultiPV-1); i++ {
				if i<NumAlphaBetaMoves {
					g.B.MakeMove(AlphaBetaMoves[i])
					collectedpv:=g.B.CollectAlphaBetaPv(Depth-1)
					Eval=AlphaBetaEvals[i]
					Pv=AlphaBetaMoves[i].ToAlgeb()
					if collectedpv!="" {
						Pv+=" "+collectedpv
					}
					g.B.UnMakeMove(AlphaBetaMoves[i])
					MultiPVIndex=i+1
					SendUciInfo()
				}
			}
			Depth++
		}
	}

	SendBestMove()
	SearchReady=true
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// MakeAlgebMove : make algeb move
// -> algeb string : algeb move
// <- bool : true = move made ok, false = failed, illegal move

func (g *TGame) MakeAlgebMove(algeb string) bool {
	g.B.InitMoveGen()
	for g.B.NextLegalMove() {
		if g.B.CurrentMove.ToAlgeb()==algeb {
			m:=g.B.CurrentMove
			g.B.MakeMove(m)
			g.Moves=append(g.Moves,m)
			return true
		}
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// SetFromFen : set game from fen
// -> fen string : fen
// <- bool : true = success, false = failed

func (g *TGame) SetFromFen(fen string) bool {
	if g.B.SetFromFen(fen) {
		g.Moves=TMoveList{}
		ClearBestMoves()
		return true
	}
	return false
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToPrintable : printable representation of game
// -> g TGame : game
// <- string : printable representation of game

func (g TGame) ToPrintable() string {
	return fmt.Sprintf("%s-> moves: %s\n-> node: %s\n",
		g.B.ToPrintable(),g.Moves.ToPrintable(),g.B.Node().ToPrintable())
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// DelMove : delete the last move from the game
// -> g *TGame : game
// <- bool : true = last move deleted ok, false = failed, no move to delete

func (g *TGame) DelMove() bool {
	l:=len(g.Moves)
	if l<=0 {
		return false
	}
	g.B.UnMakeMove(g.Moves[l-1])
	g.Moves=g.Moves[0:l-1]
	return true
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// Print : print game
// -> g TGame : game

func (g TGame) Print() {
	fmt.Printf("%s",g.ToPrintable())
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end game functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// node functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// Sort : sort node moves by eval
// -> n *TNode : node

func (n *TNode) Sort() {
	sort.Sort(n)
}

func (n *TNode) Len() int {
	return len(n.Moves)
}

func (n *TNode) Less(i,j int) bool {
	return n.Moves[i].Eval>n.Moves[j].Eval
}

func (n *TNode) Swap(i,j int) {
	n.Moves[i] , n.Moves[j] = n.Moves[j] , n.Moves[i]
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// ToPrintable : create printable representation of node
// -> n TNode : node
// <- string : printable representation of node

func (n TNode) ToPrintable() string {
	l:=len(n.Moves)
	if l<=0 {
		return "*"
	}
	buff:=""
	for i,m := range n.Moves {
		buff+=fmt.Sprintf("%s ( %d )",m.ToAlgeb(),m.Eval)
		if i<(l-1) {
			buff+=" "
		}
	}
	return buff
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// DoesNodeExist : find out whether node exists for a given position
// -> pos TPosition : position
// <- bool : true = node exists, false = node does not exist

func DoesNodeExist(pos TPosition) bool {
	_,found := Nodes[pos]
	return found
}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end node functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// Run : application run function

func Run() {
	// initialization
	Init()

	// print UCI intro message
	Printu(fmt.Sprintf("%s\n",UCI_INTRO_MESSAGE))

	// clear log
	ClearLog()

	// command interpreter loop
	// quits on "quit" command
	// Command global variable is set to "" upon declaration, so the interpreter will start
	for Command!="quit" {
		// read command line from stdin
		Commandline, _ = Reader.ReadString('\n')

		// write commandline to log
		Log(Commandline)

		// remove white spaces from beginning and end of commandline
		Commandline=strings.TrimSpace(Commandline)

		// initialize reader
		Scanner.Init(strings.NewReader(Commandline))
		Scanner.Mode=scanner.ScanIdents|scanner.ScanInts

		// if commandline contains a token, read this as command and interpret it
		if NextToken() {
			Command=Scanner.TokenText()
			if TEST {
				InterpretTestCommand()
			}
			InterpretCommand()
		}
	}

}

///////////////////////////////////////////////

///////////////////////////////////////////////
// end functions
///////////////////////////////////////////////

///////////////////////////////////////////////
// entry point of application

func main() {
	Run()
}

///////////////////////////////////////////////