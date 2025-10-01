/*
  AIGsniper copyright © 2025 - all rights reserved
  ChessEngine class refactor — multi-instance ready for evolution/GA.
  - Encapsulates state, move gen, evaluation, and search.
  - UI below binds a single instance (mainEngine) to your existing canvas/controls.
  - Safe to spin up many engines with different genomes.
*/

// S means chess board internal state
// r means row index of board
// c means column index of board

// ===== Constants & Utilities =====
const START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

// Unicode glyphs fallback
const glyphs = {
  K: "\u2654",
  Q: "\u2655",
  R: "\u2656",
  B: "\u2657",
  N: "\u2658",
  P: "\u2659",
  k: "\u265A",
  q: "\u265B",
  r: "\u265C",
  b: "\u265D",
  n: "\u265E",
  p: "\u265F",
};

// Basic Piece Values (centipawns)
const PIECE_VALUES = {
  p: -100,
  n: -320,
  b: -330,
  r: -500,
  q: -900,
  k: 0,
  P: 100,
  N: 320,
  B: 330,
  R: 500,
  Q: 900,
  K: 0,
};

let chessMultiplayer = null;

// (Optional) King PSTs kept in case you want to extend eval later
const KING_PST_MIDDLE = [
  [-30, -40, -40, -50, -50, -40, -40, -30],
  [-30, -40, -40, -50, -50, -40, -40, -30],
  [-30, -40, -40, -50, -50, -40, -40, -30],
  [-30, -40, -40, -50, -50, -40, -40, -30],
  [-20, -30, -30, -40, -40, -30, -30, -20],
  [-10, -20, -20, -20, -20, -20, -20, -10],
  [20, 20, 0, 0, 0, 0, 20, 20],
  [20, 30, 10, 0, 0, 10, 30, 20],
];
const KING_PST_END = [
  [-50, -40, -30, -20, -20, -30, -40, -50],
  [-30, -20, -10, 0, 0, -10, -20, -30],
  [-30, -10, 20, 30, 30, 20, -10, -30],
  [-30, -10, 30, 40, 40, 30, -10, -30],
  [-30, -10, 30, 40, 40, 30, -10, -30],
  [-30, -10, 20, 30, 30, 20, -10, -30],
  [-30, -30, 0, 0, 0, 0, -30, -30],
  [-50, -30, -30, -30, -30, -30, -30, -50],
];

const filesStr = "abcdefgh";
const ranksStr = "87654321";

function oppositeColor(c) {
  return c === "w" ? "b" : "w";
}
function pieceColor(p) {
  if (!p) return null;
  return p === p.toUpperCase() ? "w" : "b";
}
function onBoard(r, c) {
  return r >= 0 && r < 8 && c >= 0 && c < 8;
}

// Safe structuredClone fallback for older browsers
function deepClone(obj) {
  if (typeof structuredClone === "function") return structuredClone(obj);
  return JSON.parse(JSON.stringify(obj));
}

// ===== ChessEngine Class =====
class ChessEngine {
  constructor(fen = START_FEN, genome = null) {
    this.state = this.parseFEN(fen);
    this.moveHistory = [];
    this.positionHistory = [this.positionKey(this.state)];
    this.selected = null;
    this.legalTargets = [];

    // Add move highlighting variables
    this.lastMoveFrom = null;
    this.lastMoveTo = null;

    // AI/search
    this.searchPositions = 0;
    this.searchDepth = 0;
    this.searchStartTime = 0;
    this.pruned = 0;

    // Genome (weights for eval)
    this.genome = genome || this.getDefaultGenome();

    // UI helpers (optional)
    this.isPlayerTurn = true;
    this.flipBoard = false;
  }

  getDefaultGenome() {
    return {
      materialWeight: 1.0,
      positionalWeight: 0.5,
      // Extend with more weights later
      // kingSafetyWeight: 0.3,
      // tempoBonus: 0.1,
    };
  }

  cloneState(S = this.state) {
    return deepClone(S);
  }

  // === FEN ===
  parseFEN(fenString) {
    const fenParts = (fenString || "").trim().split(/\s+/);
    if (fenParts.length !== 6)
      throw new Error("Invalid FEN: must have 6 fields.");

    const [
      piecePlacement,
      activeColor,
      castlingField,
      enPassantField,
      halfmoveClock,
      fullmoveNumber,
    ] = fenParts;
    const ranks = piecePlacement.split("/");
    if (ranks.length !== 8) throw new Error("Invalid FEN: must have 8 ranks.");

    const newBoard = Array.from({ length: 8 }, () => Array(8).fill(""));
    for (let r = 0; r < 8; r++) {
      let fileIndex = 0;
      const rankStr = ranks[r];
      for (let i = 0; i < rankStr.length; i++) {
        const ch = rankStr[i];
        if (/[1-8]/.test(ch)) {
          fileIndex += Number(ch);
        } else if (/[prnbqkPRNBQK]/.test(ch)) {
          if (fileIndex >= 8)
            throw new Error(`Invalid FEN: too many squares on rank ${8 - r}.`);
          newBoard[r][fileIndex++] = ch;
        } else {
          throw new Error(`Invalid FEN: unexpected character "${ch}".`);
        }
      }
      if (fileIndex !== 8)
        throw new Error(`Invalid FEN: rank ${8 - r} does not fill 8 files.`);
    }

    if (activeColor !== "w" && activeColor !== "b")
      throw new Error("Invalid FEN: active color must be 'w' or 'b'.");

    const cast = castlingField === "-" ? "-" : castlingField;
    const newCastling = {
      wK: cast.includes("K"),
      wQ: cast.includes("Q"),
      bK: cast.includes("k"),
      bQ: cast.includes("q"),
    };

    let newEnPassant = null;
    if (enPassantField !== "-") {
      if (!/^[a-h][36]$/.test(enPassantField))
        throw new Error("Invalid FEN: bad en-passant square.");
      const col = filesStr.indexOf(enPassantField[0]);
      const rankNum = Number(enPassantField[1]);
      const row = 8 - rankNum;
      newEnPassant = [row, col];
    }

    const halfmove = Number.isNaN(Number(halfmoveClock))
      ? 0
      : parseInt(halfmoveClock, 10);
    const fullmove = Number.isNaN(Number(fullmoveNumber))
      ? 1
      : parseInt(fullmoveNumber, 10);

    return {
      board: newBoard,
      activeColor,
      castling: newCastling,
      enPassant: newEnPassant,
      halfmove,
      fullmove,
    };
  }

  // === Hash key ===
  positionKey(S) {
    const rows = S.board
      .map((row) => {
        let out = "",
          empty = 0;
        for (const cell of row) {
          if (!cell) empty++;
          else {
            if (empty > 0) {
              out += empty;
              empty = 0;
            }
            out += cell;
          }
        }
        if (empty > 0) out += empty;
        return out;
      })
      .join("/");
    const side = S.activeColor;
    const cast =
      (S.castling.wK ? "K" : "") +
      (S.castling.wQ ? "Q" : "") +
      (S.castling.bK ? "k" : "") +
      (S.castling.bQ ? "q" : "");
    const castStr = cast || "-";
    const ep = S.enPassant
      ? filesStr[S.enPassant[1]] + (8 - S.enPassant[0])
      : "-";
    return `${rows} ${side} ${castStr} ${ep}`;
  }

  // === Move Generation ===
  // basically works by getting a list of legal moves called psuedolegal
  // and testing if kings in check after it, if not in check add to true legal moves
  generateLegalMoves(S) {
    const pseudo = this.generatePseudoLegalMoves(S);
    const legal = [];
    for (const m of pseudo) {
      const S2 = this.cloneState(S);
      this.doMove(S2, m);
      const mover = oppositeColor(S2.activeColor);
      const kingPos = this.findKing(S2, mover);
      if (!kingPos) continue;
      if (this.isSquareAttacked(S2, kingPos[0], kingPos[1], S2.activeColor))
        continue;
      legal.push(m);
    }
    return legal;
  }

  // Generates all pseudo-legal moves for current player (without check validation).
  // Iterates through board, identifies friendly pieces, and delegates to piece-specific
  // move generators (pawns, knights, sliding pieces, king). Returns array of move strings.
  generatePseudoLegalMoves(S) {
    const moves = [];
    const color = S.activeColor;
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const p = S.board[r][c];
        if (!p) continue;
        if (pieceColor(p) !== color) continue;
        const t = p.toLowerCase();
        if (t === "p") moves.push(...this.pawnMoves(S, r, c));
        else if (t === "n") moves.push(...this.knightMoves(S, r, c));
        else if (t === "b")
          moves.push(
            ...this.slidingMoves(S, r, c, [
              [1, 1],
              [1, -1],
              [-1, 1],
              [-1, -1],
            ])
          );
        else if (t === "r")
          moves.push(
            ...this.slidingMoves(S, r, c, [
              [1, 0],
              [-1, 0],
              [0, 1],
              [0, -1],
            ])
          );
        else if (t === "q")
          moves.push(
            ...this.slidingMoves(S, r, c, [
              [1, 1],
              [1, -1],
              [-1, 1],
              [-1, -1],
              [1, 0],
              [-1, 0],
              [0, 1],
              [0, -1],
            ])
          );
        else if (t === "k") moves.push(...this.kingMoves(S, r, c));
      }
    }
    return moves;
  }

  pawnMoves(S, r, c) {
    const moves = [];
    const p = S.board[r][c];
    const col = pieceColor(p);
    const dir = col === "w" ? -1 : 1;
    const startRow = col === "w" ? 6 : 1;
    const enemy = oppositeColor(col);
    const aheadR = r + dir;

    if (onBoard(aheadR, c) && !S.board[aheadR][c]) {
      if (aheadR === 0 || aheadR === 7) {
        for (const promo of ["q", "r", "b", "n"])
          moves.push({
            from: [r, c],
            to: [aheadR, c],
            piece: p,
            capture: null,
            promotion: promo,
            flags: {},
          });
      } else {
        moves.push({
          from: [r, c],
          to: [aheadR, c],
          piece: p,
          capture: null,
          promotion: null,
          flags: {},
        });
      }
      if (r === startRow) {
        const twoR = r + 2 * dir;
        if (!S.board[twoR][c])
          moves.push({
            from: [r, c],
            to: [twoR, c],
            piece: p,
            capture: null,
            promotion: null,
            flags: { double: true },
          });
      }
    }

    for (const dc of [-1, 1]) {
      const nc = c + dc;
      const nr = r + dir;
      if (onBoard(nr, nc)) {
        const target = S.board[nr][nc];
        if (target && pieceColor(target) === enemy) {
          if (nr === 0 || nr === 7) {
            for (const promo of ["q", "r", "b", "n"])
              moves.push({
                from: [r, c],
                to: [nr, nc],
                piece: p,
                capture: target,
                promotion: promo,
                flags: {},
              });
          } else {
            moves.push({
              from: [r, c],
              to: [nr, nc],
              piece: p,
              capture: target,
              promotion: null,
              flags: {},
            });
          }
        }
        if (S.enPassant && S.enPassant[0] === nr && S.enPassant[1] === nc) {
          moves.push({
            from: [r, c],
            to: [nr, nc],
            piece: p,
            capture: col === "w" ? "p" : "P",
            promotion: null,
            flags: { enpassant: true },
          });
        }
      }
    }

    return moves;
  }

  knightMoves(S, r, c) {
    const moves = [];
    const p = S.board[r][c];
    const col = pieceColor(p);
    const enemy = oppositeColor(col);
    const deltas = [
      [2, 1],
      [2, -1],
      [-2, 1],
      [-2, -1],
      [1, 2],
      [1, -2],
      [-1, 2],
      [-1, -2],
    ];
    for (const [dr, dc] of deltas) {
      const nr = r + dr,
        nc = c + dc;
      if (!onBoard(nr, nc)) continue;
      const t = S.board[nr][nc];
      if (!t)
        moves.push({
          from: [r, c],
          to: [nr, nc],
          piece: p,
          capture: null,
          promotion: null,
          flags: {},
        });
      else if (pieceColor(t) === enemy)
        moves.push({
          from: [r, c],
          to: [nr, nc],
          piece: p,
          capture: t,
          promotion: null,
          flags: {},
        });
    }
    return moves;
  }

  slidingMoves(S, r, c, dirs) {
    const moves = [];
    const p = S.board[r][c];
    const col = pieceColor(p);
    const enemy = oppositeColor(col);
    for (const [dr, dc] of dirs) {
      let nr = r + dr,
        nc = c + dc;
      while (onBoard(nr, nc)) {
        const t = S.board[nr][nc];
        if (!t)
          moves.push({
            from: [r, c],
            to: [nr, nc],
            piece: p,
            capture: null,
            promotion: null,
            flags: {},
          });
        else {
          if (pieceColor(t) === enemy)
            moves.push({
              from: [r, c],
              to: [nr, nc],
              piece: p,
              capture: t,
              promotion: null,
              flags: {},
            });
          break;
        }
        nr += dr;
        nc += dc;
      }
    }
    return moves;
  }

  kingMoves(S, r, c) {
    const moves = [];
    const p = S.board[r][c];
    const col = pieceColor(p);
    const enemy = oppositeColor(col);
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const nr = r + dr,
          nc = c + dc;
        if (!onBoard(nr, nc)) continue;
        const t = S.board[nr][nc];
        if (!t)
          moves.push({
            from: [r, c],
            to: [nr, nc],
            piece: p,
            capture: null,
            promotion: null,
            flags: {},
          });
        else if (pieceColor(t) === enemy)
          moves.push({
            from: [r, c],
            to: [nr, nc],
            piece: p,
            capture: t,
            promotion: null,
            flags: {},
          });
      }
    }

    // castling
    if (col === "w" && r === 7 && c === 4) {
      if (S.castling.wK) {
        if (
          !S.board[7][5] &&
          !S.board[7][6] &&
          !this.isSquareAttacked(S, 7, 4, enemy) &&
          !this.isSquareAttacked(S, 7, 5, enemy) &&
          !this.isSquareAttacked(S, 7, 6, enemy)
        ) {
          moves.push({
            from: [7, 4],
            to: [7, 6],
            piece: p,
            capture: null,
            promotion: null,
            flags: { castle: "K" },
          });
        }
      }
      if (S.castling.wQ) {
        if (
          !S.board[7][3] &&
          !S.board[7][2] &&
          !S.board[7][1] &&
          !this.isSquareAttacked(S, 7, 4, enemy) &&
          !this.isSquareAttacked(S, 7, 3, enemy) &&
          !this.isSquareAttacked(S, 7, 2, enemy)
        ) {
          moves.push({
            from: [7, 4],
            to: [7, 2],
            piece: p,
            capture: null,
            promotion: null,
            flags: { castle: "Q" },
          });
        }
      }
    }
    if (col === "b" && r === 0 && c === 4) {
      if (S.castling.bK) {
        if (
          !S.board[0][5] &&
          !S.board[0][6] &&
          !this.isSquareAttacked(S, 0, 4, enemy) &&
          !this.isSquareAttacked(S, 0, 5, enemy) &&
          !this.isSquareAttacked(S, 0, 6, enemy)
        ) {
          moves.push({
            from: [0, 4],
            to: [0, 6],
            piece: p,
            capture: null,
            promotion: null,
            flags: { castle: "K" },
          });
        }
      }
      if (S.castling.bQ) {
        if (
          !S.board[0][3] &&
          !S.board[0][2] &&
          !S.board[0][1] &&
          !this.isSquareAttacked(S, 0, 4, enemy) &&
          !this.isSquareAttacked(S, 0, 3, enemy) &&
          !this.isSquareAttacked(S, 0, 2, enemy)
        ) {
          moves.push({
            from: [0, 4],
            to: [0, 2],
            piece: p,
            capture: null,
            promotion: null,
            flags: { castle: "Q" },
          });
        }
      }
    }

    return moves;
  }

  findKing(S, color) {
    const target = color === "w" ? "K" : "k";
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        if (S.board[r][c] === target) return [r, c];
      }
    }
    return null;
  }

  // === Attack detection ===
  isSquareAttacked(S, r, c, attacker) {
    // pawns
    const pd = attacker === "w" ? -1 : 1;
    const pr = r - pd;
    for (const pc of [c - 1, c + 1]) {
      if (
        onBoard(pr, pc) &&
        S.board[pr][pc] &&
        S.board[pr][pc].toLowerCase() === "p" &&
        pieceColor(S.board[pr][pc]) === attacker
      )
        return true;
    }
    // knights
    const kn = [
      [2, 1],
      [2, -1],
      [-2, 1],
      [-2, -1],
      [1, 2],
      [1, -2],
      [-1, 2],
      [-1, -2],
    ];
    for (const [dr, dc] of kn) {
      const nr = r + dr,
        nc = c + dc;
      if (
        onBoard(nr, nc) &&
        S.board[nr][nc] &&
        S.board[nr][nc].toLowerCase() === "n" &&
        pieceColor(S.board[nr][nc]) === attacker
      )
        return true;
    }
    // bishops/queens (diagonals)
    const diag = [
      [1, 1],
      [1, -1],
      [-1, 1],
      [-1, -1],
    ];
    for (const [dr, dc] of diag) {
      let nr = r + dr,
        nc = c + dc;
      while (onBoard(nr, nc)) {
        const t = S.board[nr][nc];
        if (t) {
          if (
            pieceColor(t) === attacker &&
            (t.toLowerCase() === "b" || t.toLowerCase() === "q")
          )
            return true;
          break;
        }
        nr += dr;
        nc += dc;
      }
    }
    // rooks/queens (straights)
    const straight = [
      [1, 0],
      [-1, 0],
      [0, 1],
      [0, -1],
    ];
    for (const [dr, dc] of straight) {
      let nr = r + dr,
        nc = c + dc;
      while (onBoard(nr, nc)) {
        const t = S.board[nr][nc];
        if (t) {
          if (
            pieceColor(t) === attacker &&
            (t.toLowerCase() === "r" || t.toLowerCase() === "q")
          )
            return true;
          break;
        }
        nr += dr;
        nc += dc;
      }
    }
    // king adjacency
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        const nr = r + dr,
          nc = c + dc;
        if (
          onBoard(nr, nc) &&
          S.board[nr][nc] &&
          S.board[nr][nc].toLowerCase() === "k" &&
          pieceColor(S.board[nr][nc]) === attacker
        )
          return true;
      }
    }
    return false;
  }

  // === Execute move on state S ===
  doMove(S, m) {
    const [fr, fc] = m.from;
    const [tr, tc] = m.to;
    const piece = S.board[fr][fc];
    S.board[fr][fc] = "";
    if (m.flags && m.flags.enpassant) {
      const capR = fr;
      const capC = tc;
      S.board[capR][capC] = "";
    }
    if (m.flags && m.flags.castle) {
      if (m.flags.castle === "K") {
        S.board[tr][tc] = piece;
        S.board[tr][5] = S.board[tr][7];
        S.board[tr][7] = "";
      } else if (m.flags.castle === "Q") {
        S.board[tr][tc] = piece;
        S.board[tr][3] = S.board[tr][0];
        S.board[tr][0] = "";
      }
    } else {
      if (m.promotion) {
        const isWhite = piece === piece.toUpperCase();
        const promoChar = isWhite
          ? m.promotion.toUpperCase()
          : m.promotion.toLowerCase();
        S.board[tr][tc] = promoChar;
      } else {
        S.board[tr][tc] = piece;
      }
    }
    // update castling rights
    if (piece.toLowerCase() === "k") {
      if (piece === piece.toUpperCase()) {
        S.castling.wK = false;
        S.castling.wQ = false;
      } else {
        S.castling.bK = false;
        S.castling.bQ = false;
      }
    }
    if (piece.toLowerCase() === "r") {
      if (fr === 7 && fc === 0) S.castling.wQ = false;
      if (fr === 7 && fc === 7) S.castling.wK = false;
      if (fr === 0 && fc === 0) S.castling.bQ = false;
      if (fr === 0 && fc === 7) S.castling.bK = false;
    }
    const capPiece = m.capture;
    if (capPiece && capPiece.toLowerCase() === "r") {
      if (tr === 7 && tc === 0) S.castling.wQ = false;
      if (tr === 7 && tc === 7) S.castling.wK = false;
      if (tr === 0 && tc === 0) S.castling.bQ = false;
      if (tr === 0 && tc === 7) S.castling.bK = false;
    }
    // enPassant target
    S.enPassant = null;
    if (piece.toLowerCase() === "p" && Math.abs(tr - fr) === 2) {
      S.enPassant = [(fr + tr) / 2, fc];
    }
    // halfmove/fullmove
    if (piece.toLowerCase() === "p" || m.capture) S.halfmove = 0;
    else S.halfmove++;
    if (S.activeColor === "b") S.fullmove++;
    S.activeColor = oppositeColor(S.activeColor);
  }
  // === Search ===
  minimax(state, depth, alpha, beta, isMaximizing, originalSide, sequence = []) {
    this.searchPositions++;
    // leaf
    if (depth === 0) return { score: this.evaluate(state), sequence };
    const moves = this.generateLegalMoves(state);
    const king = this.findKing(state, state.activeColor);

    // no moves -> mate or stalemate
    if (moves.length === 0) {
      if (!king) return { score: originalSide ? -Infinity : Infinity, sequence };
      const inCheck = this.isSquareAttacked(state, king[0], king[1], oppositeColor(state.activeColor));
      if (inCheck) return { score: state.activeColor === "w" ? -1e5 : 1e5, sequence };
      return { score: 0, sequence }; // stalemate
    }

    if (isMaximizing) {
      let bestScore = -Infinity;
      let bestSeq = [];
      for (const mv of moves) {
        const next = this.cloneState(state);
        this.doMove(next, mv);
        const res = this.minimax(next, depth - 1, alpha, beta, false, originalSide, [...sequence, mv]);
        if (res.score > bestScore) { bestScore = res.score; bestSeq = res.sequence; }
        alpha = Math.max(alpha, res.score);
        if (alpha >= beta) { // beta cutoff
          this.pruned++;
          break;
        }
      }
      return { score: bestScore, sequence: bestSeq };
    } else {
      let bestScore = Infinity;
      let bestSeq = [];
      for (const mv of moves) {
        const next = this.cloneState(state);
        this.doMove(next, mv);
        const res = this.minimax(next, depth - 1, alpha, beta, true, originalSide, [...sequence, mv]);
        if (res.score < bestScore) { bestScore = res.score; bestSeq = res.sequence; }
        beta = Math.min(beta, res.score);
        if (alpha >= beta) { // alpha cutoff
          this.pruned++;
          break;
        }
      }
      return { score: bestScore, sequence: bestSeq };
    }
  }

  // == Search ==
  findBestMove(depth) {
    debugLog("=== ENGINE THINKING ===\n", true);
    this.searchPositions = 0;
    this.searchDepth = depth;
    this.searchStartTime = performance.now();
    this.pruned = 0;

    const rootState = this.state;
    const legal = this.generateLegalMoves(rootState);
    let bestMove = null;
    let bestEval = rootState.activeColor === "w" ? -Infinity : Infinity;
    let bestPV = [];
    debugLog(`Evaluating ${legal.length} legal moves at depth ${depth}\n`);

    // quick mate check
    for (const m of legal) {
      const ns = this.cloneState(rootState);
      this.doMove(ns, m);
      const replies = this.generateLegalMoves(ns);
      const king = this.findKing(ns, ns.activeColor);
      if (replies.length === 0 && king && this.isSquareAttacked(ns, king[0], king[1], rootState.activeColor)) {
        debugLog(`FOUND CHECKMATE: ${moveToAlgebraic(m)}\n`);
        return m;
      }
    }

    for (const m of legal) {
      const ns = this.cloneState(rootState);
      this.doMove(ns, m);
      const res = this.minimax(ns, depth - 1, -Infinity, Infinity, ns.activeColor === "w", true, [m]);
      const score = res.score;
      const pv = res.sequence;
      const alg = moveToAlgebraic(m);
      debugLog(`${alg}: ${score}\n${this.evalDetails.breakdown}\nPrincipal variation:\n${pv.map((mv, idx) => `${idx%2==0?"White":"Black"}: ${moveToAlgebraic(mv)}`).join("\n")}\n---\n`);

      if (rootState.activeColor === "w") {
        if (score > bestEval) { bestEval = score; bestMove = m; bestPV = pv; debugLog(`↑ NEW BEST MOVE ↑\nNEW BEST: ${alg} = ${score}\n---\n`); }
      } else {
        if (score < bestEval) { bestEval = score; bestMove = m; bestPV = pv; debugLog(`↑ NEW BEST MOVE ↑\nNEW BEST: ${alg} = ${score}\n---\n`); }
      }
    }

    const timeTaken = (performance.now() - this.searchStartTime).toFixed(2);
    const pvText = bestPV.map((mv, idx) => `${idx%2==0?"White":"Black"}: ${moveToAlgebraic(mv)}`).join("\n");
    if (bestMove) {
      debugLog(`\n=== FINAL SELECTION ===\nMove: ${moveToAlgebraic(bestMove)}\nEvaluation: ${bestEval}\nPositions evaluated: ${this.searchPositions}\nBranches pruned: ${this.pruned}\nTime taken: ${timeTaken}ms\n\nPrincipal variation:\n${pvText}\n\n`, true);
    } else {
      bestMove = legal[Math.floor(Math.random() * legal.length)];
      debugLog(`\nNo best move found, selecting random: ${moveToAlgebraic(bestMove)}\nBranches pruned: ${this.pruned}\n`);
    }
    return bestMove;
  }

  // === Evaluation ===
  evaluate(S) {
    // Create evaluation details object
    this.evalDetails = {
      material: 0,
      positional: 0,
      total: 0,
      breakdown: "",
    };

    // Terminal checks first
    const legalMoves = this.generateLegalMoves(S);
    const kingPos = this.findKing(S, S.activeColor);
    if (!kingPos) {
      this.evalDetails.total = S.activeColor === "w" ? -Infinity : Infinity;
      this.evalDetails.breakdown = "King missing";
      return this.evalDetails.total;
    }

    const inCheck = this.isSquareAttacked(
      S,
      kingPos[0],
      kingPos[1],
      oppositeColor(S.activeColor)
    );

    if (legalMoves.length === 0 && inCheck) {
      this.evalDetails.total = S.activeColor === "w" ? -100000 : 100000;
      this.evalDetails.breakdown = "Checkmate";
      return this.evalDetails.total;
    }

    if (legalMoves.length === 0 && !inCheck) {
      this.evalDetails.total = 0;
      this.evalDetails.breakdown = "Stalemate";
      return this.evalDetails.total;
    }

    // Material
    let material = 0;
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const piece = S.board[r][c];
        if (!piece) continue;
        material += PIECE_VALUES[piece];
      }
    }

    // Simple positional: pawn advancement (example)
    let positional = 0;
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const piece = S.board[r][c];
        if (piece && piece.toLowerCase() === "p") {
          const baseRank = piece === "P" ? 6 : 1;
          const advancement = Math.abs(r - baseRank);
          positional += (piece === "P" ? advancement : -advancement) * 5;
        }
      }
    }

    let score = 0;
    score += material * this.genome.materialWeight;
    score += positional * this.genome.positionalWeight;

    // Store evaluation details
    this.evalDetails.material = material;
    this.evalDetails.positional = positional;
    this.evalDetails.total = score;
    this.evalDetails.breakdown =
      `Material: ${material} × ${this.genome.materialWeight} = ${material * this.genome.materialWeight
      }\n` +
      `Positional: ${positional} × ${this.genome.positionalWeight} = ${positional * this.genome.positionalWeight
      }\n` +
      `Total: ${score}`;

    return score;
  }

  // === Public helpers ===
  makeMove(m) {
    const mCopy = deepClone(m);
    
    // Store the move coordinates for highlighting (using instance variables)
    this.lastMoveFrom = mCopy.from;
    this.lastMoveTo = mCopy.to;
    
    this.doMove(this.state, mCopy);
    this.moveHistory.push(mCopy);
    this.positionHistory.push(this.positionKey(this.state));
    return mCopy;
  }

  // Draw detection
  isFiftyMoveDraw(S = this.state) {
    return S.halfmove >= 100;
  }
  isThreefoldRepetition() {
    const key = this.positionKey(this.state);
    let count = 0;
    for (const k of this.positionHistory) if (k === key) count++;
    return count >= 3;
  }
  isInsufficientMaterial(S = this.state) {
    let pawns = 0,
      rooks = 0,
      queens = 0,
      bishops = 0,
      knights = 0;
    const bishopSquares = [];
    for (let r = 0; r < 8; r++) {
      for (let c = 0; c < 8; c++) {
        const p = S.board[r][c];
        if (!p) continue;
        const t = p.toLowerCase();
        if (t === "p") pawns++;
        else if (t === "r") rooks++;
        else if (t === "q") queens++;
        else if (t === "b") {
          bishops++;
          bishopSquares.push((r + c) & 1);
        } else if (t === "n") knights++;
      }
    }
    if (pawns > 0 || rooks > 0 || queens > 0) return false;
    const minor = bishops + knights;
    if (minor === 0) return true;
    if (minor === 1) return true;
    if (minor === 2) {
      if (knights === 2) return true;
      if (bishops === 2) {
        const allParity = bishopSquares.every((p) => p === bishopSquares[0]);
        if (allParity) return true;
      }
    }
    return false;
  }
}

// ======== UI Binding to a Single Engine Instance ========
// Canvas & drawing
const canvas = document.getElementById("boardCanvas");
const ctx = canvas.getContext("2d");
const size = canvas.width;
const sq = size / 8;

// Player selection elements
const whitePlayerSelect = document.getElementById("whitePlayer");
const blackPlayerSelect = document.getElementById("blackPlayer");
const startButton = document.getElementById("btnStart");

// Game state variables
let gameStarted = false;
let whitePlayerType = "human";
let blackPlayerType = "bot";

// Images
const pieceImages = {};
let imagesLoaded = 0;
const piecesList = [
  "wK",
  "wQ",
  "wR",
  "wB",
  "wN",
  "wP",
  "bK",
  "bQ",
  "bR",
  "bB",
  "bN",
  "bP",
];
const totalImages = piecesList.length;
const imageSize = 64;

function loadPieceImages() {
  piecesList.forEach((code) => {
    const img = new Image();
    img.onload = () => {
      imagesLoaded++;
      if (imagesLoaded === totalImages) {
        document.getElementById("loading").style.display = "none";
        document.getElementById("game").style.display = "flex";
        render();
      }
    };
    img.onerror = () => {
      console.error(`Failed to load images/${code}.png`);
      imagesLoaded++;
      if (imagesLoaded === totalImages) {
        document.getElementById("loading").style.display = "none";
        document.getElementById("game").style.display = "flex";
        render();
      }
    };
    img.src = `images/${code}.png`;
    pieceImages[code] = img;
  });
}

// Main engine instance used by the UI
const mainEngine = new ChessEngine(START_FEN);

// Render uses the engine encapsulated state
function render() {
  const S = mainEngine.state;
  const flipBoard = mainEngine.flipBoard;
  ctx.clearRect(0, 0, size, size);

  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const displayR = flipBoard ? 7 - r : r;
      const displayC = flipBoard ? 7 - c : c;
      const x = displayC * sq;
      const y = displayR * sq;
      const light = (r + c) % 2 === 0;

      // draw square
      ctx.fillStyle = light
        ? getComputedStyle(document.documentElement).getPropertyValue("--light")
        : getComputedStyle(document.documentElement).getPropertyValue("--dark");
      ctx.fillRect(x, y, sq, sq);

      // file labels (a–h) along bottom
      if (r === 7) {
        ctx.fillStyle = light ? "#000" : "#fff";
        ctx.font = "12px Arial";
        ctx.textAlign = "right";
        ctx.textBaseline = "bottom";
        const file = filesStr[flipBoard ? 7 - c : c];
        ctx.fillText(file, x + sq - 6, y + sq - 6);
      }

      // rank labels (1–8) along left
      if (c === 0) {
        ctx.fillStyle = light ? "#000" : "#fff";
        ctx.font = "12px Arial";
        ctx.textAlign = "left";
        ctx.textBaseline = "top";
        const rank = ranksStr[flipBoard ? r : 7 - r];
        ctx.fillText(rank, x + 6, y + 6);
      }
    }
  }

  // highlight last move
  if (mainEngine.lastMoveFrom && mainEngine.lastMoveTo) {
    ctx.fillStyle = "rgba(255, 255, 0, 0.3)";
    drawRect(mainEngine.lastMoveFrom[0], mainEngine.lastMoveFrom[1]);
    drawRect(mainEngine.lastMoveTo[0], mainEngine.lastMoveTo[1]);
  }

  // highlight selected square + legal moves
  if (mainEngine.selected) {
    const [sr, sc] = mainEngine.selected;
    ctx.fillStyle = getComputedStyle(document.documentElement).getPropertyValue(
      "--highlight"
    );
    drawRect(sr, sc);
    for (const t of mainEngine.legalTargets) {
      ctx.fillStyle = t.capture
        ? getComputedStyle(document.documentElement).getPropertyValue(
          "--capture"
        )
        : getComputedStyle(document.documentElement).getPropertyValue(
          "--highlight"
        );
      drawRect(t.to[0], t.to[1]);
    }
  }

  // draw pieces
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const p = S.board[r][c];
      if (!p) continue;
      const displayR = flipBoard ? 7 - r : r;
      const displayC = flipBoard ? 7 - c : c;
      const x = displayC * sq;
      const y = displayR * sq;
      const color = p === p.toUpperCase() ? "w" : "b";
      const imageCode = color + p.toUpperCase();
      if (pieceImages[imageCode] && pieceImages[imageCode].width > 0) {
        const center = (sq - imageSize) / 2;
        ctx.drawImage(
          pieceImages[imageCode],
          x + center,
          y + center,
          imageSize,
          imageSize
        );
      } else {
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.font = sq * 0.75 + "px serif";
        ctx.fillStyle = color === "w" ? "#fff" : "#000";
        ctx.fillText(glyphs[p] || p, x + sq / 2, y + sq / 2);
      }
    }
  }
}

function drawRect(r, c) {
  const displayR = mainEngine.flipBoard ? 7 - r : r;
  const displayC = mainEngine.flipBoard ? 7 - c : c;
  ctx.fillRect(displayC * sq, displayR * sq, sq, sq);
}

// Eval bar (wrap class evaluate)
function evaluatePosition(S) {
  return mainEngine.evaluate(S || mainEngine.state);
}

function updateEvalBar() {
  const container = document.getElementById("evalBarContainer");
  const bar = document.getElementById("evalBar");
  const scoreElement = document.getElementById("evalScore");
  const showEvalBar = true;
  if (!showEvalBar) {
    container.style.display = "none";
    return;
  }
  container.style.display = "block";

  const score = evaluatePosition(mainEngine.state);
  const scoreFormatted = (score / 100).toFixed(2);
  const scoreText = (score > 0 ? "+" : "") + scoreFormatted;
  scoreElement.textContent = scoreText;

  const maxEvalForDisplay = 500;
  const cappedScore = Math.max(
    Math.min(score, maxEvalForDisplay),
    -maxEvalForDisplay
  );
  let percentage = 50 + (cappedScore / maxEvalForDisplay) * 50;
  if (score < 0) percentage = 100 - percentage;
  bar.style.height = percentage + "%";
}

// Promotion overlay (uses mainEngine)
function showPromotionOverlay(move) {
  const overlay = document.getElementById("promotionOverlay");
  overlay.innerHTML = "";
  overlay.style.display = "flex";
  const box = document.createElement("div");
  box.className = "promoBox";
  const isWhite =
    mainEngine.state.board[move.from[0]][move.from[1]] ===
    mainEngine.state.board[move.from[0]][move.from[1]].toUpperCase();
  const pieces = isWhite ? ["Q", "R", "B", "N"] : ["q", "r", "b", "n"];

  for (let i = 0; i < 4; i++) {
    const code = (isWhite ? "w" : "b") + pieces[i].toUpperCase();
    const b = document.createElement("div");
    b.className = "promoBtn";

    if (pieceImages[code] && pieceImages[code].width > 0) {
      b.style.backgroundImage = `url('images/${code}.png')`;
      b.style.backgroundSize = "contain";
      b.style.backgroundRepeat = "no-repeat";
      b.style.backgroundPosition = "center";
    } else {
      b.textContent = glyphs[pieces[i]] || pieces[i];
      b.style.display = "flex";
      b.style.alignItems = "center";
      b.style.justifyContent = "center";
      b.style.fontSize = "30px";
    }

    b.onclick = () => {
      move.promotion = pieces[i].toLowerCase();
      overlay.style.display = "none";
      mainEngine.makeMove(move);
      mainEngine.selected = null;
      mainEngine.legalTargets = [];

      // Render immediately
      render();
      refreshPanels();

      // Check if next player is a bot
      checkAndMakeBotMove();
      checkEnd();
    };

    box.appendChild(b);
  }

  overlay.appendChild(box);
}

// Input handling - UPDATED for multiplayer
canvas.addEventListener("click", (e) => {
    if (!gameStarted) return;
    
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;
    const c = Math.floor(x / sq),
        r = Math.floor(y / sq);
    const logicalC = mainEngine.flipBoard ? 7 - c : c;
    const logicalR = mainEngine.flipBoard ? 7 - r : r;
    
    onSquareClick(logicalR, logicalC);
});

function onSquareClick(r, c) {
  // Check if it's a human player's turn
  const currentPlayerType = mainEngine.state.activeColor === "w" ? whitePlayerType : blackPlayerType;
  if (currentPlayerType !== "human") return;

  const p = mainEngine.state.board[r][c];

  if (mainEngine.selected) {
    const match = mainEngine.legalTargets.find(
      (t) => t.to[0] === r && t.to[1] === c
    );
    if (match) {
      if (match.promotion) {
        showPromotionOverlay(match);
        return;
      }

      // Make player's move immediately
      mainEngine.makeMove(match);
      mainEngine.selected = null;
      mainEngine.legalTargets = [];

      // Render immediately after player's move
      render();
      updateEvalBar();
      refreshPanels();

      // Check if next player is a bot
      checkAndMakeBotMove();
      return;
    }

    if (p && pieceColor(p) === mainEngine.state.activeColor) {
      mainEngine.selected = [r, c];
      mainEngine.legalTargets = mainEngine
        .generateLegalMoves(mainEngine.state)
        .filter((m) => m.from[0] === r && m.from[1] === c);
      render();
    } else {
      mainEngine.selected = null;
      mainEngine.legalTargets = [];
      render();
    }
  } else {
    if (p && pieceColor(p) === mainEngine.state.activeColor) {
      mainEngine.selected = [r, c];
      mainEngine.legalTargets = mainEngine
        .generateLegalMoves(mainEngine.state)
        .filter((m) => m.from[0] === r && m.from[1] === c);
      render();
    }
  }
}

// Check if next move should be made by a bot
function checkAndMakeBotMove() {
  const currentPlayerType = mainEngine.state.activeColor === "w" ? whitePlayerType : blackPlayerType;
  if (currentPlayerType === "bot") {
    // Start AI move after a short delay to allow UI to update
    setTimeout(makeAIMove, 50);
  }
}

// reasoning output handling
function debugLog(message, clear = false) {
  const debugOutput = document.getElementById("debugOutput");
  if (clear) {
    debugOutput.textContent = message;
  } else {
    debugOutput.textContent += message;
  }
  debugOutput.scrollTop = debugOutput.scrollHeight;
}

// Move list / state panel helpers
function refreshPanels() {
  const movelist = document.getElementById("movelist");
  movelist.textContent = mainEngine.moveHistory
    .map((mv, i) => `${i + 1}. ${moveToAlgebraic(mv)}`)
    .join("\n");
  document.getElementById("gamestate").textContent = JSON.stringify(
    {
      activeColor: mainEngine.state.activeColor,
      castling: mainEngine.state.castling,
      enPassant: mainEngine.state.enPassant,
      halfmove: mainEngine.state.halfmove,
      fullmove: mainEngine.state.fullmove,
    },
    null,
    2
  );
}

function moveToAlgebraic(m) {
  const from = filesStr[m.from[1]] + ranksStr[m.from[0]];
  const to = filesStr[m.to[1]] + ranksStr[m.to[0]];
  let s = from + to;
  if (m.promotion) s += "=" + m.promotion.toUpperCase();
  if (m.flags && m.flags.castle) s = m.flags.castle === "K" ? "O-O" : "O-O-O";
  if (m.flags && m.flags.enpassant) s += "e.p.";
  if (m.capture) s = from[0] + "x" + to;
  return s;
}

// AI driver - make it asynchronous
function makeAIMove() {
  // Only make AI move if it's bot's turn
  const currentPlayerType = mainEngine.state.activeColor === "w" ? whitePlayerType : blackPlayerType;
  if (currentPlayerType !== "bot") return;

  // Show thinking indicator immediately
  debugLog("AI is thinking...");

  // Use setTimeout to allow UI to update before AI starts thinking
  setTimeout(() => {
    const legal = mainEngine.generateLegalMoves(mainEngine.state);
    if (legal.length === 0) {
      checkEnd();
      return;
    }

    const best = mainEngine.findBestMove(2); // Reduced depth for faster response
    if (best.promotion) best.promotion = "q";
    mainEngine.makeMove(best);

    render();
    updateEvalBar();
    refreshPanels();
    
    // Check if next player is a bot
    checkAndMakeBotMove();
    checkEnd();
  }, 100); // Small delay to ensure UI updates
}

// Draw / game end checks
function checkEnd() {
  const legal = mainEngine.generateLegalMoves(mainEngine.state);
  if (legal.length === 0) {
    const kingPos = mainEngine.findKing(
      mainEngine.state,
      mainEngine.state.activeColor
    );
    if (!kingPos) {
      alert("Game over (king missing)");
      gameStarted = false;
      return;
    }
    const inCheck = mainEngine.isSquareAttacked(
      mainEngine.state,
      kingPos[0],
      kingPos[1],
      oppositeColor(mainEngine.state.activeColor)
    );
    if (inCheck) {
      alert(
        "Checkmate! " +
        (mainEngine.state.activeColor === "w" ? "Black" : "White") +
        " wins."
      );
      gameStarted = false;
      return;
    } else {
      alert("Stalemate.");
      gameStarted = false;
      return;
    }
  }
  // notify of game ending
  if (mainEngine.isThreefoldRepetition()) {
    alert("Draw by threefold repetition.");
    gameStarted = false;
    return;
  }
  if (mainEngine.isFiftyMoveDraw()) {
    alert("Draw by fifty-move rule.");
    gameStarted = false;
    return;
  }
  if (mainEngine.isInsufficientMaterial()) {
    alert("Draw by insufficient material.");
    gameStarted = false;
    return;
  }
}

// Start game function
function startGame() {
  whitePlayerType = whitePlayerSelect.value;
  blackPlayerType = blackPlayerSelect.value;
  
  // Reset the game
  mainEngine.state = mainEngine.parseFEN(START_FEN);
  mainEngine.moveHistory = [];
  mainEngine.positionHistory = [mainEngine.positionKey(mainEngine.state)];
  mainEngine.selected = null;
  mainEngine.legalTargets = [];
  
  gameStarted = true;
  
  render();
  updateEvalBar();
  refreshPanels();
  
  // If white is a bot, start with AI move
  if (whitePlayerType === "bot") {
    checkAndMakeBotMove();
  }
}

// Controls
function loadFEN() {
  const fenString = document.getElementById("fenInput").value;
  const errorElement = document.getElementById("fenError");
  if (!fenString) {
    errorElement.textContent = "Please enter a FEN string.";
    errorElement.style.display = "block";
    return;
  }
  try {
    mainEngine.state = mainEngine.parseFEN(fenString);
    mainEngine.moveHistory = [];
    mainEngine.positionHistory = [mainEngine.positionKey(mainEngine.state)];
    mainEngine.selected = null;
    mainEngine.legalTargets = [];
    
    // Clear move highlights using engine instance variables
    mainEngine.lastMoveFrom = null;
    mainEngine.lastMoveTo = null;
    
    document.getElementById("movelist").textContent = "";
    document.getElementById("gamestate").textContent = JSON.stringify(
      {
        activeColor: mainEngine.state.activeColor,
        castling: mainEngine.state.castling,
        enPassant: mainEngine.state.enPassant,
        halfmove: mainEngine.state.halfmove,
        fullmove: mainEngine.state.fullmove,
      },
      null,
      2
    );
    errorElement.style.display = "none";
    render();
    updateEvalBar();
  } catch (err) {
    errorElement.textContent = err.message;
    errorElement.style.display = "block";
  }
}

// Event listeners
document.getElementById("btnLoadFEN").addEventListener("click", loadFEN);
document.getElementById("fenInput").addEventListener("keypress", function (e) {
  if (e.key === "Enter") loadFEN();
});

document.getElementById("btnReset").addEventListener("click", () => {
  mainEngine.state = mainEngine.parseFEN(START_FEN);
  mainEngine.moveHistory = [];
  mainEngine.positionHistory = [mainEngine.positionKey(mainEngine.state)];
  mainEngine.selected = null;
  mainEngine.legalTargets = [];
  
  // Clear move highlights using engine instance variables
  mainEngine.lastMoveFrom = null;
  mainEngine.lastMoveTo = null;
  
  render();
  updateEvalBar();
  refreshPanels();
});

document.getElementById("btnFlip").addEventListener("click", () => {
  mainEngine.flipBoard = !mainEngine.flipBoard;
  render();
  updateEvalBar();
});

// Start button event listener
startButton.addEventListener("click", startGame);

// Tournament mode variables
let tournamentMode = false;
let tournamentGames = [];
let tournamentWorkers = [];
const TOURNAMENT_GAME_COUNT = 4;

// Boot
if (typeof window !== 'undefined') {
(function boot() {
  loadPieceImages();
  
  // Only render if not in tournament mode
  if (!tournamentMode) {
    render();
    updateEvalBar();
    const fenInput = document.getElementById("fenInput");
    if (fenInput) fenInput.value = START_FEN;
  }
})();
}
if (typeof self !== 'undefined') {
  // Worker thread: expose ChessEngine
  self.ChessEngine = ChessEngine;
}
// Add these variables at the top with other game state variables
let currentGenome = null;

// Add this function to create genome input fields
function createGenomeInputs(genome) {
  const container = document.getElementById('genomeInputs');
  container.innerHTML = '';
  
  for (const [key, value] of Object.entries(genome)) {
    const group = document.createElement('div');
    group.className = 'genome-input-group';
    
    const label = document.createElement('label');
    label.textContent = key + ':';
    
    const input = document.createElement('input');
    input.type = 'number';
    input.step = '0.1';
    input.value = value;
    input.id = `genome-${key}`;
    
    group.appendChild(label);
    group.appendChild(input);
    container.appendChild(group);
  }
}

// Add function to get current genome from inputs
function getGenomeFromInputs() {
  const genome = {};
  const inputs = document.querySelectorAll('#genomeInputs input');
  
  inputs.forEach(input => {
    const key = input.id.replace('genome-', '');
    genome[key] = parseFloat(input.value) || 0;
  });
  
  return genome;
}

// Add function to update genome status message
function updateGenomeStatus(message, isError = false) {
  const status = document.getElementById('genomeStatus');
  status.textContent = message;
  status.className = `genome-status ${isError ? 'error' : 'success'}`;
  
  // Clear status after 3 seconds
  setTimeout(() => {
    status.textContent = '';
    status.className = 'genome-status';
  }, 3000);
}

// Add function to generate random genome
function generateRandomGenome() {
  // Start with default genome structure
  const defaultGenome = (new ChessEngine()).getDefaultGenome();
  const randomGenome = {};
  
  for (const [key, value] of Object.entries(defaultGenome)) {
    // Random value between 0.1 and 2.0
    randomGenome[key] = (Math.random() * 1.9 + 0.1).toFixed(2);
  }
  
  return randomGenome;
}
// Tournament button event listener
document.getElementById("btnTournament").addEventListener("click", function() {
  startTournamentMode(null);
});

function startTournamentMode(genome = null) {
  tournamentMode = true;
  
  // Hide unnecessary elements
  document.getElementById("debugPanel").classList.add("hidden");
  document.getElementById("controls").classList.add("hidden");
  document.getElementById("game").classList.remove("hidden");
  document.getElementById("game").classList.add("tournament-mode");
  
  // Create tournament layout with genome controls
  const gameElement = document.getElementById("game");
  gameElement.innerHTML = `
    <div class="tournament-header">AI Tournament</div>
    
    <div class="tournament-genome-controls">
      <h3>AI Genome Configuration</h3>
      <div id="genomeInputs"></div>
      <div class="genome-buttons">
        <button id="btnDefaultGenome">Default Genome</button>
        <button id="btnRandomGenome">Random Genome</button>
        <button id="btnStartTournament">Start Tournament</button>
      </div>
      <div id="genomeStatus" class="genome-status"></div>
    </div>
    
    <div class="tournament-boards" id="tournamentBoards"></div>
    <div class="tournament-controls">
      <button id="btnStopTournament">Stop Tournament</button>
      <button id="btnPauseTournament">Pause/Resume</button>
    </div>
  `;
  
  // Initialize with default genome or the provided one
  currentGenome = genome || (new ChessEngine()).getDefaultGenome();
  createGenomeInputs(currentGenome);
  
  // Add event listeners for genome controls
  document.getElementById('btnDefaultGenome').addEventListener('click', () => {
    const defaultGenome = (new ChessEngine()).getDefaultGenome();
    currentGenome = defaultGenome;
    createGenomeInputs(defaultGenome);
    updateGenomeStatus('Default genome loaded');
  });
  
  document.getElementById('btnRandomGenome').addEventListener('click', () => {
    const randomGenome = generateRandomGenome();
    currentGenome = randomGenome;
    createGenomeInputs(randomGenome);
    updateGenomeStatus('Random genome generated');
  });
  
  document.getElementById("btnStartTournament").addEventListener("click", () => {
    currentGenome = getGenomeFromInputs();
    initializeTournamentGames(currentGenome);
  });
  
  document.getElementById("btnStopTournament").addEventListener("click", stopTournament);
  document.getElementById("btnPauseTournament").addEventListener("click", togglePauseTournament);
}

function initializeTournamentGames(startingGenome = null) {
  tournamentGames = [];
  tournamentWorkers = [];
  
  // Use the provided genome or fall back to the current one
  const genomeToUse = startingGenome || currentGenome || (new ChessEngine()).getDefaultGenome();
  
  // Create tournament boards
  const boardsContainer = document.getElementById("tournamentBoards");
  boardsContainer.innerHTML = '';
  
  for (let i = 0; i < TOURNAMENT_GAME_COUNT; i++) {
    const boardContainer = document.createElement("div");
    boardContainer.className = "tournament-board-container";
    
    // Create genome display strings for both AIs
    const genomeString1 = Object.entries(genomeToUse)
      .map(([key, value]) => `${getGenomeAbbreviation(key)}:${value.toFixed(1)}`)
      .join(' ');
    
    const genomeString2 = Object.entries(genomeToUse)
      .map(([key, value]) => `${getGenomeAbbreviation(key)}:${value.toFixed(1)}`)
      .join(' ');
    
    boardContainer.innerHTML = `
      <div class="tournament-info" id="tournamentInfo${i}">
        <div>White: ${genomeString1}</div>
        <div>Black: ${genomeString2}</div>
      </div>
      <canvas class="tournament-canvas" id="tournamentCanvas${i}" width="320" height="320"></canvas>
      <div class="tournament-info" id="tournamentEval${i}">Evaluation: 0.00</div>
    `;
    boardsContainer.appendChild(boardContainer);
    
    const canvas = document.getElementById(`tournamentCanvas${i}`);
    const game = {
      canvas,
      ctx: canvas.getContext("2d"),
      info: document.getElementById(`tournamentInfo${i}`),
      eval: document.getElementById(`tournamentEval${i}`),
      paused: false,
      gameOver: false,
      ready: false,
      engine: null,
      genome: {...genomeToUse},
      // Store the original genome strings for both players
      genomeStringWhite: genomeString1,
      genomeStringBlack: genomeString2
    };
    tournamentGames.push(game);
    
    // Rest of the worker initialization code remains the same
    const workerCode = `
      ${ChessEngine.toString()}

      const filesStr = "abcdefgh";
      const ranksStr = "87654321";
      const PIECE_VALUES = { p:-100,n:-320,b:-330,r:-500,q:-900,k:0,P:100,N:320,B:330,R:500,Q:900,K:0 };
      function oppositeColor(c){ return c==='w'?'b':'w'; }
      function pieceColor(p){ if(!p) return null; return p===p.toUpperCase()?'w':'b'; }
      function onBoard(r,c){ return r>=0&&r<8&&c>=0&&c<8; }
      function deepClone(o){ return typeof structuredClone==='function'?structuredClone(o):JSON.parse(JSON.stringify(o)); }
      function moveToAlgebraic(m){
        const from = filesStr[m.from[1]]+ranksStr[m.from[0]];
        const to = filesStr[m.to[1]]+ranksStr[m.to[0]];
        let s = from+to;
        if(m.promotion) s+='='+m.promotion.toUpperCase();
        if(m.flags && m.flags.castle) s = m.flags.castle==='K'?'O-O':'O-O-O';
        if(m.flags && m.flags.enpassant) s+='e.p.';
        if(m.capture) s = from[0]+'x'+to;
        return s;
      }
      function debugLog(...args){}
      function isGameOver(engine) {
        const legal = engine.generateLegalMoves(engine.state);
        return legal.length === 0 || engine.isThreefoldRepetition() || engine.isFiftyMoveDraw() || engine.isInsufficientMaterial();
      }
      function getGameResult(engine) {
        const legal = engine.generateLegalMoves(engine.state);
        if (legal.length > 0) {
          if(engine.isThreefoldRepetition()) return "Draw by repetition";
          if(engine.isFiftyMoveDraw()) return "Draw by 50-move rule";
          if(engine.isInsufficientMaterial()) return "Draw by insufficient material";
          return "Game in progress";
        }
        const kingPos = engine.findKing(engine.state, engine.state.activeColor);
        if(!kingPos) return "Invalid position";
        const inCheck = engine.isSquareAttacked(engine.state, kingPos[0], kingPos[1], oppositeColor(engine.state.activeColor));
        return inCheck ? \`Checkmate - \${engine.state.activeColor==='w'?'Black':'White'} wins\` : "Stalemate";
      }

      self.addEventListener('message', e=>{
        const { type, data } = e.data;

        if(type==='init') {
          self.engine = new ChessEngine(data.fen, data.genome || null);
          self.postMessage({ type:'ready' });
        }

        if(type==='getMove' && self.engine) {
          if(isGameOver(self.engine)) {
            self.postMessage({ type:'move', data:{ move:null, evaluation:self.engine.evaluate(self.engine.state), gameOver:true, result:getGameResult(self.engine) } });
          } else {
            const move = self.engine.findBestMove(data.depth);
            self.engine.makeMove(move);
            // Send the move coordinates for highlighting
            self.postMessage({ type:'move', data:{ 
              move, 
              evaluation:self.engine.evaluate(self.engine.state),
              lastMoveFrom: self.engine.lastMoveFrom,
              lastMoveTo: self.engine.lastMoveTo
            } });
          }
        }

        if(type==='makeMove' && self.engine) {
          self.engine.makeMove(data.move);
          self.postMessage({ type:'moveApplied' });
        }
      });
    `;

    const blob = new Blob([workerCode], { type: 'application/javascript' });
    const worker = new Worker(URL.createObjectURL(blob));

    worker.onmessage = e => {
      const { type, data } = e.data;
      if(type === 'ready') {
        tournamentGames[i].ready = true;
        console.log(`Worker ${i} ready`);
        // Don't change the info text - keep the genome display
        makeAIMoveInTournament(i);
      } else {
        handleWorkerMessage(i, e.data);
      }
    };

    tournamentWorkers.push(worker);
    worker.postMessage({ 
      type: 'init', 
      data: { 
        fen: START_FEN,
        genome: {...genomeToUse} // Pass the genome to the worker
      } 
    });
  }
  
  updateGenomeStatus('Tournament started with custom genome!');
}

// Helper function to get genome abbreviation
function getGenomeAbbreviation(fullName) {
  const abbreviations = {
    'materialWeight': 'M',
    'positionalWeight': 'P',
    'kingSafetyWeight': 'K',
    'tempoBonus': 'T',
    'mobilityWeight': 'Mb',
    'pawnStructureWeight': 'Ps',
    'centerControlWeight': 'Cc'
    // Add more abbreviations as you add more genome weights
  };
  
  return abbreviations[fullName] || fullName.substring(0, 2);
}

// Handle worker messages
function handleWorkerMessage(gameIndex, message) {
  const game = tournamentGames[gameIndex];
  
  switch (message.type) {
    case 'move':
      if (message.data.gameOver) {
        // Append the result to the genome display
        game.info.innerHTML = `
          <div>${game.genomeStringWhite}</div>
          <div>${game.genomeStringBlack}</div>
          <div>${message.data.result}</div>
        `;
        game.gameOver = true;
        return;
      }

      // Initialize board if needed
      if (!game.state || !game.state.board) {
        game.state = { board: fenToBoard(START_FEN) };
      }

      // Apply move to board
      game.state.board = applyMoveToBoard(game.state.board, message.data.move);

      // Save last move
      game.lastMove = message.data.move;

      renderTournamentBoard(gameIndex);

      game.eval.textContent = `Evaluation: ${(message.data.evaluation / 100).toFixed(2)}`;

      if (!game.paused) {
        setTimeout(() => makeAIMoveInTournament(gameIndex), 100);
      }
      break;

    case 'moveApplied':
      break;
  }
}

// Convert FEN to board array
function fenToBoard(fen) {
  const board = [];
  const rows = fen.split(' ')[0].split('/');
  for (let r = 0; r < 8; r++) {
    const row = [];
    for (let c of rows[r]) {
      if (/[1-8]/.test(c)) {
        for (let i = 0; i < parseInt(c); i++) row.push(null);
      } else {
        row.push(c);
      }
    }
    board.push(row);
  }
  return board;
}

// Apply move to board array
function applyMoveToBoard(board, move) {
  const [fromR, fromC] = move.from;
  const [toR, toC] = move.to;
  const piece = board[fromR][fromC];
  board[toR][toC] = board[fromR][fromC];
  board[fromR][fromC] = null;
  
  if (move.promotion) {
    // Preserve the color of the original piece when promoting
    const isWhite = piece === piece.toUpperCase();
    board[toR][toC] = isWhite ? move.promotion.toUpperCase() : move.promotion.toLowerCase();
  }
  
  // Add castling / en passant logic if needed
  return board;
}

// Render the tournament board
function renderTournamentBoard(gameIndex) {
  const game = tournamentGames[gameIndex];
  const S = game.state;
  if (!S || !S.board) return;

  const canvas = game.canvas;
  const ctx = game.ctx;
  const sq = canvas.width / 8;

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // Draw checkerboard
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      ctx.fillStyle = (r + c) % 2 === 0 ? "#f0d9b5" : "#b58863";
      ctx.fillRect(c * sq, r * sq, sq, sq);
    }
  }

  // Highlight last move for tournament games
  if (game.lastMove) {
    ctx.fillStyle = "rgba(255, 255, 0, 0.3)";
    ctx.fillRect(game.lastMove.from[1] * sq, game.lastMove.from[0] * sq, sq, sq);
    ctx.fillRect(game.lastMove.to[1] * sq, game.lastMove.to[0] * sq, sq, sq);
  }

  // Draw pieces (existing code remains the same)
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const p = S.board[r][c];
      if (!p) continue;

      const color = p === p.toUpperCase() ? 'w' : 'b';
      const imageCode = color + p.toUpperCase();

      if (pieceImages[imageCode] && pieceImages[imageCode].width > 0) {
        const center = (sq - 32) / 2;
        ctx.drawImage(pieceImages[imageCode], c * sq + center, r * sq + center, 32, 32);
      } else {
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.font = (sq * 0.6) + "px serif";
        ctx.fillStyle = color === "w" ? "#fff" : "#000";
        ctx.fillText(glyphs[p] || p, c * sq + sq / 2, r * sq + sq / 2);
      }
    }
  }
}

function makeAIMoveInTournament(gameIndex) {
  const game = tournamentGames[gameIndex];
  if (game.paused || game.gameOver) return;

  tournamentWorkers[gameIndex].postMessage({
    type: 'getMove',
    data: { depth: 2 } // adjust for speed
  });
}

function isGameOver(engine) {
  const legal = engine.generateLegalMoves(engine.state);
  if (legal.length === 0) return true;
  
  return engine.isThreefoldRepetition() || 
         engine.isFiftyMoveDraw() || 
         engine.isInsufficientMaterial();
}

function getGameResult(engine) {
  const legal = engine.generateLegalMoves(engine.state);
  if (legal.length > 0) {
    if (engine.isThreefoldRepetition()) return "Draw by repetition";
    if (engine.isFiftyMoveDraw()) return "Draw by 50-move rule";
    if (engine.isInsufficientMaterial()) return "Draw by insufficient material";
    return "Game in progress";
  }
  
  const kingPos = engine.findKing(engine.state, engine.state.activeColor);
  if (!kingPos) return "Invalid position";
  
  const inCheck = engine.isSquareAttacked(
    engine.state,
    kingPos[0],
    kingPos[1],
    oppositeColor(engine.state.activeColor)
  );
  
  return inCheck ? 
    `Checkmate - ${engine.state.activeColor === "w" ? "Black" : "White"} wins` : 
    "Stalemate";
}

function stopTournament() {
  // Terminate all workers
  tournamentWorkers.forEach(worker => worker.terminate());
  tournamentWorkers = [];
  tournamentGames = [];
  
  // Return to normal view
  tournamentMode = false;
  location.reload(); // Simple way to reset everything
}

function togglePauseTournament() {
  const pauseButton = document.getElementById("btnPauseTournament");
  const allPaused = tournamentGames.every(game => game.paused);
  
  tournamentGames.forEach(game => {
    game.paused = !allPaused;
    
    // If we're resuming and the game isn't over, make a move
    if (allPaused && !game.gameOver) {
      makeAIMoveInTournament(tournamentGames.indexOf(game));
    }
  });
  
  pauseButton.textContent = allPaused ? "Pause" : "Resume";
}

class ChessMultiplayer {
    constructor(chessEngine) {
        this.engine = chessEngine;
        this.clientId = null;
        this.username = 'ChessPlayer_' + Math.floor(Math.random() * 1000);
        this.serverUrl = 'https://multiplayer-6vlc.onrender.com';
        this.isConnected = false;
        this.currentGame = null;
        this.pendingChallenges = [];
        this.pollingInterval = null;
        this.isChallenger = false;
        this.selectedColor = null;
        this.ourColor = null; // Track our color
        this.gameStarted = false; // Track if multiplayer game has started
        
        this.initializeMultiplayerUI();
    }

    initializeMultiplayerUI() {
        document.getElementById('btnMultiplayer').addEventListener('click', () => {
            this.toggleMultiplayerPanel();
        });

        document.getElementById('btnSendChallenge').addEventListener('click', () => {
            const username = document.getElementById('challengeUsername').value;
            this.sendChallenge(username);
        });

        document.getElementById('btnCloseMultiplayer').addEventListener('click', () => {
            this.hideMultiplayerPanel();
        });

        document.getElementById('btnDisconnect').addEventListener('click', () => {
            this.disconnect();
        });
    }

    async connect() {
        try {
            const response = await fetch(`${this.serverUrl}/api/join`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ 
                    username: this.username,
                    isChessClient: true
                })
            });
            
            const data = await response.json();
            if (data.success) {
                this.clientId = data.clientId;
                this.isConnected = true;
                this.startPolling();
                this.updateUI();
                this.updateStatus('Connected to multiplayer server');
                this.updateOnlinePlayers();
            } else if (data.isPending) {
                this.clientId = data.clientId;
                this.updateStatus('Waiting for moderator approval...');
                this.startPolling();
            } else {
                this.updateStatus('Failed to connect: ' + data.error);
            }
        } catch (error) {
            console.error('Failed to connect:', error);
            this.updateStatus('Connection failed - server may be offline');
        }
    }

    startPolling() {
        if (this.pollingInterval) {
            clearInterval(this.pollingInterval);
        }
        
        this.pollingInterval = setInterval(async () => {
            await this.checkForUpdates();
        }, 2000);
    }

    async checkForUpdates() {
        if (!this.clientId) return;
        
        try {
            const response = await fetch(`${this.serverUrl}/api/get-updates`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ clientId: this.clientId })
            });
            
            const data = await response.json();
            if (data.events && data.events.length > 0) {
                this.handleEvents(data.events);
            }
        } catch (error) {
            console.error('Polling error:', error);
        }
    }

    handleEvents(events) {
        events.forEach(event => {
            console.log('Received event:', event);
            switch (event.event) {
                case 'chess_invitation':
                    this.handleChessInvitation(event.data);
                    break;
                case 'chess_game_ready':
                    this.handleGameReady(event.data);
                    break;
                case 'chess_game_started':
                    this.handleGameStarted(event.data);
                    break;
                case 'chess_move_made':
                    this.handleOpponentMove(event.data);
                    break;
                case 'users_list':
                    this.updateOnlinePlayers(event.data);
                    break;
                case 'join_approved':
                    this.handleJoinApproved(event.data);
                    break;
                case 'join_rejected':
                    this.handleJoinRejected(event.data);
                    break;
                case 'color_selected':
                    this.handleColorSelection(event.data);
                    break;
                case 'chess_game_cancelled':
                    this.handleGameCancelled(event.data);
                    break;
                case 'kicked':
                    this.handleKicked(event.data);
                    break;
                case 'server_deactivated':
                    this.handleServerDeactivated(event.data);
                    break;
            }
        });
    }

    handleChessInvitation(data) {
        console.log('Received chess invitation:', data);
        
        this.pendingChallenges.push({
            gameId: data.gameId,
            challenger: data.challenger,
            challengerId: data.challengerId,
            receivedAt: Date.now()
        });
        
        this.updateChallengesList();
        this.showChallengeNotification(data.challenger, data.gameId);
    }

    showChallengeNotification(challenger, gameId) {
        const notification = document.createElement('div');
        notification.style.cssText = `
            position: fixed;
            top: 20px;
            right: 20px;
            background: var(--dark-panel);
            padding: 15px;
            border-radius: 8px;
            border: 2px solid var(--accent);
            z-index: 10000;
            max-width: 300px;
        `;
        
        notification.innerHTML = `
            <strong>Chess Challenge!</strong>
            <p>${challenger} has challenged you!</p>
            <div style="display: flex; gap: 10px; margin-top: 10px;">
                <button onclick="chessMultiplayer.acceptChallenge('${gameId}')" 
                        style="padding: 5px 10px; background: var(--accent); border: none; border-radius: 4px; cursor: pointer;">
                    Accept
                </button>
                <button onclick="chessMultiplayer.declineChallenge('${gameId}')" 
                        style="padding: 5px 10px; background: #666; border: none; border-radius: 4px; cursor: pointer;">
                    Decline
                </button>
            </div>
        `;
        
        document.body.appendChild(notification);
        
        setTimeout(() => {
            if (document.body.contains(notification)) {
                document.body.removeChild(notification);
            }
        }, 30000);
    }

    async acceptChallenge(gameId) {
        try {
            const response = await fetch(`${this.serverUrl}/api/accept-chess-invitation`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ 
                    clientId: this.clientId, 
                    gameId 
                })
            });
            
            const data = await response.json();
            if (data.success) {
                this.currentGame = data.gameState;
                this.isChallenger = false;
                this.removeChallenge(gameId);
                this.showGameSetupPanel();
                this.updateStatus(`Accepted challenge from ${data.gameState.challengerName}`);
                this.removeChallengeNotifications();
            } else {
                this.updateStatus('Failed to accept challenge: ' + data.error);
            }
        } catch (error) {
            console.error('Failed to accept challenge:', error);
            this.updateStatus('Error accepting challenge');
        }
    }

    async declineChallenge(gameId) {
        this.removeChallenge(gameId);
        this.removeChallengeNotifications();
        this.updateStatus('Challenge declined');
    }

    removeChallenge(gameId) {
        this.pendingChallenges = this.pendingChallenges.filter(challenge => challenge.gameId !== gameId);
        this.updateChallengesList();
    }

    removeChallengeNotifications() {
        const notifications = document.querySelectorAll('div');
        notifications.forEach(div => {
            if (div.innerHTML.includes('Chess Challenge!')) {
                document.body.removeChild(div);
            }
        });
    }

    updateChallengesList() {
        const challengesList = document.getElementById('pendingChallengesList');
        if (!challengesList) return;
        
        challengesList.innerHTML = '';
        
        if (this.pendingChallenges.length === 0) {
            challengesList.innerHTML = '<div style="padding: 10px; text-align: center; color: #888;">No pending challenges</div>';
            return;
        }
        
        this.pendingChallenges.forEach(challenge => {
            const challengeElement = document.createElement('div');
            challengeElement.className = 'player-item';
            challengeElement.innerHTML = `
                <div>
                    <strong>${challenge.challenger}</strong>
                    <div style="font-size: 12px; color: #888;">${new Date(challenge.receivedAt).toLocaleTimeString()}</div>
                </div>
                <div>
                    <button onclick="chessMultiplayer.acceptChallenge('${challenge.gameId}')" 
                            style="padding: 4px 8px; margin: 2px; background: var(--accent); border: none; border-radius: 4px; cursor: pointer;">
                        Accept
                    </button>
                    <button onclick="chessMultiplayer.declineChallenge('${challenge.gameId}')" 
                            style="padding: 4px 8px; margin: 2px; background: #666; border: none; border-radius: 4px; cursor: pointer;">
                        Decline
                    </button>
                </div>
            `;
            challengesList.appendChild(challengeElement);
        });
    }

    async sendChallenge(username) {
        if (!username || !this.clientId) {
            alert('Please connect to the server first');
            return;
        }
        
        try {
            const response = await fetch(`${this.serverUrl}/api/active-users`);
            const data = await response.json();
            
            if (!data.users) {
                alert('Failed to fetch user list');
                return;
            }
            
            const targetUser = data.users.find(u => u.username === username);
            if (!targetUser) {
                alert('User not found or offline');
                return;
            }
            
            const challengeResponse = await fetch(`${this.serverUrl}/api/create-chess-game`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ 
                    clientId: this.clientId,
                    opponentId: targetUser.clientId,
                    challengerName: this.username
                })
            });
            
            if (!challengeResponse.ok) {
                throw new Error(`Server error: ${challengeResponse.status}`);
            }
            
            const challengeData = await challengeResponse.json();
            if (challengeData.success) {
                this.currentGame = challengeData.gameState;
                this.isChallenger = true;
                this.updateStatus(`Challenge sent to ${username} - waiting for acceptance`);
                this.showGameSetupPanel();
            } else {
                this.updateStatus('Failed to send challenge: ' + challengeData.error);
            }
        } catch (error) {
            console.error('Failed to send challenge:', error);
            this.updateStatus('Error sending challenge: ' + error.message);
        }
    }

    showGameSetupPanel() {
        this.hideMultiplayerPanel();
        
        const setupHTML = `
            <div id="gameSetupPanel" style="
                position: fixed;
                top: 50%;
                left: 50%;
                transform: translate(-50%, -50%);
                background: var(--dark-panel);
                padding: 20px;
                border-radius: 10px;
                z-index: 1000;
                width: 400px;
                text-align: center;
            ">
                <h3>Game Setup</h3>
                <div id="setupStatus">Waiting for opponent to accept...</div>
                <div style="margin: 20px 0; display: ${this.isChallenger ? 'block' : 'none'};" id="colorSelectionSection">
                    <h4>Choose Your Color</h4>
                    <div style="display: flex; justify-content: center; gap: 20px; margin: 15px 0;">
                        <button id="btnSelectWhite" class="color-btn" style="
                            padding: 10px 20px;
                            background: #f0d9b5;
                            color: #000;
                            border: 2px solid #b58863;
                            border-radius: 5px;
                            cursor: pointer;
                        ">Play as White</button>
                        <button id="btnSelectBlack" class="color-btn" style="
                            padding: 10px 20px;
                            background: #b58863;
                            color: #fff;
                            border: 2px solid #000;
                            border-radius: 5px;
                            cursor: pointer;
                        ">Play as Black</button>
                    </div>
                </div>
                <div id="startGameSection" style="display: none;">
                    <button id="btnStartMultiplayerGame" style="
                        padding: 10px 20px;
                        background: var(--accent);
                        color: white;
                        border: none;
                        border-radius: 5px;
                        cursor: pointer;
                        margin: 10px 0;
                    ">Start Game</button>
                </div>
                <button id="btnCancelSetup" style="
                    padding: 8px 16px;
                    background: #666;
                    color: white;
                    border: none;
                    border-radius: 5px;
                    cursor: pointer;
                ">Cancel</button>
            </div>
        `;
        
        const existingPanel = document.getElementById('gameSetupPanel');
        if (existingPanel) existingPanel.remove();
        
        document.body.insertAdjacentHTML('beforeend', setupHTML);
        
        document.getElementById('btnSelectWhite')?.addEventListener('click', () => {
            this.selectColor('white');
        });
        
        document.getElementById('btnSelectBlack')?.addEventListener('click', () => {
            this.selectColor('black');
        });
        
        document.getElementById('btnStartMultiplayerGame').addEventListener('click', () => {
            this.startMultiplayerGame();
        });
        
        document.getElementById('btnCancelSetup').addEventListener('click', () => {
            this.cancelGameSetup();
        });
    }

    async selectColor(color) {
        this.selectedColor = color;
        
        document.querySelectorAll('.color-btn').forEach(btn => {
            btn.style.border = '2px solid #666';
        });
        document.getElementById(`btnSelect${color.charAt(0).toUpperCase() + color.slice(1)}`)
            .style.border = '2px solid var(--accent)';
        
        document.getElementById('startGameSection').style.display = 'block';
        document.getElementById('setupStatus').textContent = `You selected ${color}. Ready to start!`;
        
        try {
            await fetch(`${this.serverUrl}/api/chess-color-select`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    clientId: this.clientId,
                    gameId: this.currentGame.id,
                    color: color
                })
            });
        } catch (error) {
            console.error('Failed to send color selection:', error);
        }
    }

    handleColorSelection(data) {
        if (this.currentGame && this.currentGame.id === data.gameId) {
            document.getElementById('setupStatus').textContent = 
                `Opponent selected ${data.color}. You will play as ${data.color === 'white' ? 'black' : 'white'}.`;
            
            if (!this.isChallenger) {
                document.getElementById('startGameSection').style.display = 'none';
                this.selectedColor = data.color === 'white' ? 'black' : 'white';
            }
        }
    }

    async startMultiplayerGame() {
        if (!this.currentGame || !this.selectedColor) {
            alert('Please select a color first');
            return;
        }
        
        try {
            const response = await fetch(`${this.serverUrl}/api/start-chess-game`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    clientId: this.clientId,
                    gameId: this.currentGame.id,
                    challengerColor: this.selectedColor
                })
            });
            
            const data = await response.json();
            if (data.success) {
                this.currentGame = data.gameState;
                this.setupMultiplayerGame();
                this.removeGameSetupPanel();
            } else {
                alert('Failed to start game: ' + data.error);
            }
        } catch (error) {
            console.error('Failed to start game:', error);
            alert('Error starting game');
        }
    }

    handleGameReady(data) {
        if (data.gameState && data.gameState.id === this.currentGame?.id) {
            this.currentGame = data.gameState;
            
            if (!this.isChallenger) {
                document.getElementById('setupStatus').textContent = 
                    `Challenge accepted! Waiting for ${data.gameState.challengerName} to choose color...`;
                document.getElementById('startGameSection').style.display = 'none';
                document.querySelectorAll('.color-btn').forEach(btn => {
                    btn.style.display = 'none';
                });
            }
        }
    }

    handleGameStarted(data) {
        if (data.gameState && (!this.currentGame || this.currentGame.id !== data.gameState.id)) {
            this.currentGame = data.gameState;
        }
        
        this.setupMultiplayerGame();
        this.removeGameSetupPanel();
    }

    setupMultiplayerGame() {
        if (!this.currentGame) return;
        
        try {
            // Determine our color
            this.ourColor = this.currentGame.playerWhite === this.clientId ? 'white' : 'black';
            const opponentName = this.ourColor === 'white' ? this.currentGame.blackName : this.currentGame.whiteName;
            
            this.updateGameUIForMultiplayer(this.ourColor, opponentName);
            
            // Reset the engine with the game's FEN position
            this.engine.state = this.engine.parseFEN(this.currentGame.fen || START_FEN);
            this.engine.moveHistory = [];
            this.engine.positionHistory = [this.engine.positionKey(this.engine.state)];
            this.engine.selected = null;
            this.engine.legalTargets = [];
            
            // Set board orientation - player should see from their perspective
            this.engine.flipBoard = this.ourColor === 'black';
            
            // Mark multiplayer game as started
            this.gameStarted = true;
            gameStarted = true; // Global game started flag
            
            // Disable player selection controls
            document.getElementById('whitePlayer').disabled = true;
            document.getElementById('blackPlayer').disabled = true;
            document.getElementById('btnStart').style.display = 'none';
            
            render();
            updateEvalBar();
            refreshPanels();
            
            this.updateStatus(`Playing vs ${opponentName} (you are ${this.ourColor}) - ${this.isOurTurn() ? 'Your turn!' : 'Waiting for opponent...'}`);
            
        } catch (error) {
            console.error('Error setting up multiplayer game:', error);
            this.updateStatus('Error setting up game');
        }
    }

    updateGameUIForMultiplayer(ourColor, opponentName) {
        const whiteLabel = document.querySelector('.player-top .player-label');
        const blackLabel = document.querySelector('.player-bottom .player-label');
        
        if (ourColor === 'white') {
            whiteLabel.textContent = 'You (White)';
            blackLabel.textContent = `${opponentName} (Black)`;
        } else {
            whiteLabel.textContent = `${opponentName} (White)`;
            blackLabel.textContent = 'You (Black)';
        }
        
        document.getElementById('btnStart').style.display = 'none';
    }

    removeGameSetupPanel() {
        const panel = document.getElementById('gameSetupPanel');
        if (panel) panel.remove();
    }

    cancelGameSetup() {
        if (this.currentGame) {
            fetch(`${this.serverUrl}/api/cancel-chess-game`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    clientId: this.clientId,
                    gameId: this.currentGame.id
                })
            }).catch(console.error);
            
            this.currentGame = null;
            this.isChallenger = false;
            this.selectedColor = null;
            this.ourColor = null;
            this.gameStarted = false;
        }
        this.removeGameSetupPanel();
        this.updateStatus('Game setup cancelled');
    }

    handleGameCancelled(data) {
        this.currentGame = null;
        this.isChallenger = false;
        this.selectedColor = null;
        this.ourColor = null;
        this.gameStarted = false;
        this.removeGameSetupPanel();
        this.updateStatus('Game was cancelled by the other player');
        
        // Re-enable controls
        document.getElementById('whitePlayer').disabled = false;
        document.getElementById('blackPlayer').disabled = false;
        document.getElementById('btnStart').style.display = 'block';
    }

    handleKicked(data) {
        this.disconnect();
        alert('You have been kicked from the server');
    }

    handleServerDeactivated(data) {
        this.disconnect();
        alert('Server has been deactivated. Please try again later.');
    }

    handleOpponentMove(data) {
        if (this.currentGame && this.currentGame.id === data.gameId) {
            console.log('Processing opponent move:', data.move);
            
            // Update the game state
            this.currentGame = data.gameState;
            
            // Apply the move to our local engine
            this.engine.makeMove(data.move);
            
            // Update the board
            render();
            updateEvalBar();
            refreshPanels();
            
            this.updateStatus(`Opponent moved - ${this.isOurTurn() ? 'Your turn!' : 'Waiting for opponent...'}`);
        }
    }

    handleJoinApproved(data) {
        this.clientId = data.clientId;
        this.username = data.username;
        this.isConnected = true;
        this.updateStatus(`Approved! Connected as ${this.username}`);
        this.updateUI();
        this.updateOnlinePlayers();
    }

    handleJoinRejected(data) {
        this.updateStatus(`Join rejected: ${data.reason}`);
        this.disconnect();
    }

    // FIXED: Proper move validation and sending
    async makeMove(move) {
        console.log('makeMove called:', { 
            currentGame: !!this.currentGame, 
            clientId: !!this.clientId, 
            gameStarted: this.gameStarted,
            move: move 
        });
        
        if (!this.currentGame || !this.clientId || !this.gameStarted) {
            console.log('Cannot make move: game not ready');
            this.updateStatus('Game not ready');
            return false;
        }
        
        // FIX: Use the ORIGINAL engine state (before any local moves) for validation
        const currentTurn = this.engine.state.activeColor; // This should still be our turn
        const isOurTurn = (currentTurn === 'w' && this.ourColor === 'white') || 
                        (currentTurn === 'b' && this.ourColor === 'black');
        
        console.log('Turn validation (ORIGINAL STATE):', {
            engineTurn: currentTurn,
            ourColor: this.ourColor,
            isOurTurn: isOurTurn
        });
        
        // Validate it's our turn using local engine state
        if (!isOurTurn) {
            console.log('Not your turn!');
            this.updateStatus('Not your turn! Wait for opponent.');
            return false;
        }
        
        // Validate we're moving our own pieces
        const piece = this.engine.state.board[move.from[0]][move.from[1]];
        if (!piece) {
            console.log('No piece at selected square');
            this.updateStatus('Invalid move - no piece selected');
            return false;
        }
        
        const pieceColor = piece === piece.toUpperCase() ? 'white' : 'black';
        if (pieceColor !== this.ourColor) {
            console.log('Cannot move opponent pieces!');
            this.updateStatus('Cannot move opponent pieces!');
            return false;
        }
        
        try {
          console.log('Sending move to server...');
          
          // ADD TIMEOUT HANDLING
          const controller = new AbortController();
          const timeoutId = setTimeout(() => controller.abort(), 10000); // 10 second timeout
          
          const response = await fetch(`${this.serverUrl}/api/chess-move`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
              clientId: this.clientId,
              gameId: this.currentGame.id,
              move: move
            }),
            signal: controller.signal
          });
          
          clearTimeout(timeoutId);
          
          const data = await response.json();
          console.log('Server response:', data);
          
          if (data.success) {
            this.currentGame = data.gameState;
            this.updateStatus(`Move sent - waiting for opponent...`);
            return true;
          } else {
            this.updateStatus('Move failed: ' + data.error);
            return false;
          }
        } catch (error) {
          console.error('Failed to send move:', error);
          
          // SPECIFIC TIMEOUT HANDLING
          if (error.name === 'AbortError') {
            this.updateStatus('Move timeout - server not responding');
            console.error('Server timeout - attempting reconnection...');
            // Optional: Implement reconnection logic here
          } else {
            this.updateStatus('Error sending move: ' + error.message);
          }
          return false;
        }
      }

    async updateOnlinePlayers(users = null) {
        const playersList = document.getElementById('onlinePlayersList');
        if (!playersList) return;
        
        playersList.innerHTML = '';
        
        if (!users) {
            try {
                const response = await fetch(`${this.serverUrl}/api/active-users`);
                const data = await response.json();
                users = data.users || [];
            } catch (error) {
                console.error('Failed to fetch online players:', error);
                users = [];
            }
        }
        
        const otherPlayers = users.filter(user => user.clientId !== this.clientId);
        
        if (otherPlayers.length === 0) {
            playersList.innerHTML = '<div style="padding: 10px; text-align: center; color: #888;">No other players online</div>';
            return;
        }
        
        otherPlayers.forEach(user => {
            const playerElement = document.createElement('div');
            playerElement.className = 'player-item';
            playerElement.innerHTML = `
                <span>${user.username} ${user.isMod ? '(Mod)' : ''}</span>
                <button onclick="chessMultiplayer.challengeUser('${user.username}')">Challenge</button>
            `;
            playersList.appendChild(playerElement);
        });
    }

    challengeUser(username) {
        document.getElementById('challengeUsername').value = username;
        this.sendChallenge(username);
    }

    updateStatus(message) {
        const statusElement = document.getElementById('multiplayerStatus');
        if (statusElement) {
            statusElement.textContent = message;
        }
        console.log('Multiplayer Status:', message);
    }

    updateUI() {
        const statusElement = document.getElementById('multiplayerStatus');
        if (statusElement) {
            statusElement.textContent = `Connected as ${this.username} (${this.clientId})`;
        }
    }

    // Add this function to ai.js in the ChessMultiplayer class
    getCurrentTurnFromFEN(fen) {
        if (!fen) return 'w'; // Default to white if no FEN
        const parts = fen.split(' ');
        return parts.length > 1 ? parts[1] : 'w';
    }

    // Update the isOurTurn method to use FEN consistently:
    isOurTurn() {
        if (!this.currentGame || !this.ourColor) {
            console.log('Turn check failed: no game or color');
            return false;
        }
        
        try {
            // Use FEN for turn detection (most reliable)
            const currentTurn = this.getCurrentTurnFromFEN(this.currentGame.fen);
            const isOurTurn = (currentTurn === 'w' && this.ourColor === 'white') || 
                            (currentTurn === 'b' && this.ourColor === 'black');
            
            console.log('Turn check (FEN-based):', {
                fen: this.currentGame.fen,
                currentTurn: currentTurn,
                ourColor: this.ourColor,
                isOurTurn: isOurTurn
            });
            
            return isOurTurn;
        } catch (error) {
            console.error('Error detecting turn:', error);
            return false;
        }
    }
    
    toggleMultiplayerPanel() {
        const panel = document.getElementById('multiplayerPanel');
        if (panel) {
            panel.classList.toggle('hidden');
            
            if (!panel.classList.contains('hidden')) {
                if (!this.isConnected && !this.clientId) {
                    this.connect();
                } else {
                    this.updateOnlinePlayers();
                    this.updateChallengesList();
                    this.updateActiveGames();
                }
            }
        }
    }

    updateActiveGames() {
        const gamesList = document.getElementById('activeGamesList');
        if (!gamesList) return;
        
        gamesList.innerHTML = '';
        
        if (!this.currentGame) {
            gamesList.innerHTML = '<div style="padding: 10px; text-align: center; color: #888;">No active games</div>';
            return;
        }
        
        const opponentName = this.ourColor === 'white' ? this.currentGame.blackName : this.currentGame.whiteName;
        const isOurTurn = this.isOurTurn();
        
        const gameElement = document.createElement('div');
        gameElement.className = 'player-item';
        gameElement.innerHTML = `
            <div>
                <strong>vs ${opponentName}</strong>
                <div style="font-size: 12px; color: #888;">
                    You are ${this.ourColor} • ${isOurTurn ? 'Your turn' : 'Opponent\'s turn'}
                </div>
            </div>
            <button onclick="chessMultiplayer.resumeGame()" 
                    style="padding: 4px 8px; background: var(--accent); border: none; border-radius: 4px; cursor: pointer;">
                Resume
            </button>
        `;
        gamesList.appendChild(gameElement);
    }

    resumeGame() {
        if (this.currentGame) {
            this.setupMultiplayerGame();
            this.hideMultiplayerPanel();
        }
    }

    hideMultiplayerPanel() {
        const panel = document.getElementById('multiplayerPanel');
        if (panel) {
            panel.classList.add('hidden');
        }
    }

    disconnect() {
        if (this.pollingInterval) {
            clearInterval(this.pollingInterval);
            this.pollingInterval = null;
        }
        
        if (this.clientId) {
            fetch(`${this.serverUrl}/api/leave`, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ clientId: this.clientId })
            }).catch(console.error);
        }
        
        this.isConnected = false;
        this.clientId = null;
        this.currentGame = null;
        this.pendingChallenges = [];
        this.isChallenger = false;
        this.selectedColor = null;
        this.ourColor = null;
        this.gameStarted = false;
        this.updateStatus('Disconnected');
        
        this.removeGameSetupPanel();
        
        // Re-enable controls
        document.getElementById('whitePlayer').disabled = false;
        document.getElementById('blackPlayer').disabled = false;
        document.getElementById('btnStart').style.display = 'block';
    }
}

// FIXED: Override the square click handler for multiplayer
function createMultiplayerSquareClickHandler() {
    const originalOnSquareClick = onSquareClick;
    
    return function(r, c) {
        // If we're in a multiplayer game, use multiplayer logic
        if (chessMultiplayer && chessMultiplayer.gameStarted) {
            handleMultiplayerSquareClick(r, c);
        } else {
            // Otherwise use original single-player logic
            originalOnSquareClick(r, c);
        }
    };
}

// FIXED: Multiplayer-specific square click handler
function handleMultiplayerSquareClick(r, c) {
    console.log('Multiplayer square click:', {r, c, ourColor: chessMultiplayer.ourColor, ourTurn: chessMultiplayer.isOurTurn()});
    
    if (!chessMultiplayer.isOurTurn()) {
        chessMultiplayer.updateStatus('Not your turn! Wait for opponent.');
        return;
    }
    
    const p = mainEngine.state.board[r][c];
    console.log('Piece at square:', p);
    
    if (mainEngine.selected) {
        const match = mainEngine.legalTargets.find(
            t => t.to[0] === r && t.to[1] === c
        );
        
        if (match) {
            console.log('Move match found:', match);
            
            // Validate we're moving our own piece
            const selectedPiece = mainEngine.state.board[mainEngine.selected[0]][mainEngine.selected[1]];
            if (!selectedPiece) {
                console.log('No piece at selected square - clearing selection');
                mainEngine.selected = null;
                mainEngine.legalTargets = [];
                render();
                return;
            }
            
            const selectedPieceColor = selectedPiece === selectedPiece.toUpperCase() ? 'white' : 'black';
            
            if (selectedPieceColor !== chessMultiplayer.ourColor) {
                chessMultiplayer.updateStatus('Cannot move opponent pieces!');
                mainEngine.selected = null;
                mainEngine.legalTargets = [];
                render();
                return;
            }

            // DOUBLE-CHECK: It's still our turn before proceeding
            if (!chessMultiplayer.isOurTurn()) {
                chessMultiplayer.updateStatus('Turn ended while selecting move!');
                mainEngine.selected = null;
                mainEngine.legalTargets = [];
                render();
                return;
            }
            
            if (match.promotion) {
                console.log('Showing promotion overlay');
                showPromotionOverlay(match);
                return;
            }

            // Send move to server FIRST, before making local move
            console.log('Sending move to server');
            chessMultiplayer.makeMove(match).then(success => {
                if (success) {
                    // Only make local move if server accepted it
                    console.log('Server accepted move, applying locally');
                    const moveCopy = deepClone(match);
                    mainEngine.makeMove(moveCopy);
                    mainEngine.selected = null;
                    mainEngine.legalTargets = [];

                    // Render after successful server response
                    render();
                    updateEvalBar();
                    refreshPanels();

                    chessMultiplayer.updateStatus('Move sent - waiting for opponent...');
                } else {
                    chessMultiplayer.updateStatus('Failed to send move - try again');
                    // Don't make local move if server rejected it
                }
            });
            return;
        }

        // If clicking on another piece of ours, change selection
        if (p) {
            const pieceColor = p === p.toUpperCase() ? 'white' : 'black';
            
            // Only allow selecting our own pieces
            if (pieceColor === chessMultiplayer.ourColor) {
                mainEngine.selected = [r, c];
                mainEngine.legalTargets = mainEngine
                    .generateLegalMoves(mainEngine.state)
                    .filter(m => m.from[0] === r && m.from[1] === c);
                render();
            } else {
                chessMultiplayer.updateStatus('Cannot select opponent pieces!');
                mainEngine.selected = null;
                mainEngine.legalTargets = [];
                render();
            }
        } else {
            // Clicked on empty square - clear selection
            mainEngine.selected = null;
            mainEngine.legalTargets = [];
            render();
        }
    } else {
        // No current selection - try to select a piece
        if (p) {
            const pieceColor = p === p.toUpperCase() ? 'white' : 'black';
            
            // Only allow selecting our own pieces
            if (pieceColor === chessMultiplayer.ourColor) {
                mainEngine.selected = [r, c];
                mainEngine.legalTargets = mainEngine
                    .generateLegalMoves(mainEngine.state)
                    .filter(m => m.from[0] === r && m.from[1] === c);
                render();
                console.log('Selected piece, legal moves:', mainEngine.legalTargets.length);
            } else {
                chessMultiplayer.updateStatus('Cannot select opponent pieces!');
            }
        } else {
            chessMultiplayer.updateStatus('No piece at this square');
        }
    }
}

// Initialize multiplayer when the page loads
document.addEventListener('DOMContentLoaded', () => {
    chessMultiplayer = new ChessMultiplayer(mainEngine);
    
    // Override the square click handler
    onSquareClick = createMultiplayerSquareClickHandler();
});
