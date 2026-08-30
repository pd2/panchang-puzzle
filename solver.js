// Panchang puzzle solver.
//
// Formalizes the board (from puzzleBorder's polygon) and the 10 SVG pieces as
// polyominoes on a unit grid, and solves the "tile everything except the 3
// grey squares" exact-cover problem with plain backtracking (the search space
// is tiny -- 10 pieces, ~48 cells -- so no need for full Algorithm X/DLX).
//
// Runs unmodified in the browser (attaches `window.PanchangSolver`) and under
// Node (module.exports), so it can be unit-tested standalone before being
// wired into script.js.

(function (root) {
  'use strict';

  // pcsList order, front/sym classification and board geometry all mirror
  // the constants already used in script.js -- kept in sync deliberately.
  const PCS_LIST = ["sSpcs", "sLpcs", "Qpcs", "bSpcs", "lSpcs", "bLpcs", "Ipcs", "Cpcs", "eLpcs", "Tpcs"];
  const FRONT_PCS = new Set(["Cpcs", "eLpcs", "Tpcs"]); // classList contains 'front': never actually mirrored
  const SYM_PCS = new Set(["sSpcs", "bSpcs"]);          // classList contains 'sym': only 2 of the 4 rotation labels are reachable

  // Base shapes (angle=0, mirrored=false), rasterized once from the SVG
  // polygon `points=` attributes in index.html (unit = 100px grid).
  const BASE_SHAPES = {
    Tpcs:  [[0, 0], [1, 0], [2, 0], [1, 1], [1, 2]],
    sLpcs: [[0, 0], [0, 1], [1, 1], [2, 1]],
    bLpcs: [[0, 0], [0, 1], [1, 1], [2, 1], [3, 1]],
    lSpcs: [[0, 0], [1, 0], [1, 1], [2, 1], [3, 1]],
    Cpcs:  [[0, 0], [2, 0], [0, 1], [1, 1], [2, 1]],
    Ipcs:  [[0, 0], [0, 1], [1, 1], [0, 2], [0, 3]],
    eLpcs: [[0, 0], [0, 1], [0, 2], [1, 2], [2, 2]],
    sSpcs: [[0, 0], [0, 1], [1, 1], [1, 2]],
    bSpcs: [[0, 0], [1, 0], [1, 1], [1, 2], [2, 2]],
    Qpcs:  [[0, 0], [0, 1], [1, 1], [0, 2], [1, 2]],
  };

  // Board: the actual drawn puzzleBorder polygon (index.html) is a 6x8
  // rectangle (grid x:0-5, y:0-7) with a 1-wide, 3-tall bump on the right
  // (grid x:6, y:2-4). That's 51 cells. NOTE: this differs from
  // computePcsPos()'s own placement-validity test in script.js, which uses
  // `x==6 && y>1 && y<6` (grid y:2-5, one row too many/off-by-one vs. what's
  // actually drawn) -- a pre-existing bug in script.js, not reproduced here.
  // Using the correct 51-cell board is what makes this an exact cover: the
  // 10 pieces sum to exactly 48 cells, and 51 - 3 excluded = 48.
  function isOnBoard(x, y) {
    if (x >= 0 && y >= 0 && x < 6 && y < 8) return true;
    if (x === 6 && y >= 2 && y <= 4) return true;
    return false;
  }

  function boardCells() {
    const cells = [];
    for (let y = 0; y < 8; y++) {
      for (let x = 0; x < 7; x++) {
        if (isOnBoard(x, y)) cells.push([x, y]);
      }
    }
    return cells; // 51 cells
  }

  // --- geometry: exact integer cell-space equivalents of the SVG transform
  // stack (translate * scale(mirror) * rotate), derived from where each
  // transformed unit cell's *center* point lands. See solver-derivation
  // notes: rotate is applied first, then mirror, matching baseVal order
  // [translate, scale, rotate].
  function rotateCell([x, y], angle) {
    switch (angle) {
      case 0: return [x, y];
      case 90: return [-y - 1, x];
      case 180: return [-x - 1, -y - 1];
      case 270: return [y, -x - 1];
      default: throw new Error("bad angle " + angle);
    }
  }
  function mirrorCell([x, y]) {
    return [-x - 1, y];
  }

  // xOfs/yOfs correction, exactly mirroring computePcsPos()/placePieces() in
  // script.js, needed to convert a chosen pixel-grid anchor (A,B) into the
  // (xPos,yPos) logical grid position that ends up in the hex encoding.
  function ofsFor(angle, mirrored, isFront) {
    let xOfs = 0, yOfs = 0;
    if (angle === 90) xOfs -= 1;
    if (angle === 180) { xOfs -= 1; yOfs -= 1; }
    if (angle === 270) yOfs -= 1;
    if (mirrored && !isFront) {
      if (angle !== 90 && angle !== 180) xOfs -= 1;
      else xOfs += 1;
    }
    return { xOfs, yOfs };
  }

  // All (angle, mirrored) combinations actually reachable through the UI for
  // a given piece -- matters for sym pieces, where only 2 of the 4 nominal
  // rotation labels are ever produced by clicking (see transformPcs()'s
  // rotation branch in script.js), even though geometrically shape(0)==shape(180)
  // and shape(90)==shape(270) for those pieces.
  function reachableOrientations(id) {
    if (FRONT_PCS.has(id)) {
      return [0, 90, 180, 270].map(angle => ({ angle, mirrored: false }));
    }
    if (SYM_PCS.has(id)) {
      return [
        { angle: 0, mirrored: false }, { angle: 270, mirrored: false },
        { angle: 0, mirrored: true }, { angle: 90, mirrored: true },
      ];
    }
    const out = [];
    for (const angle of [0, 90, 180, 270]) {
      out.push({ angle, mirrored: false });
      out.push({ angle, mirrored: true });
    }
    return out;
  }

  function transformShape(id, angle, mirrored) {
    const base = BASE_SHAPES[id];
    const isFront = FRONT_PCS.has(id);
    return base.map(c => {
      let rc = rotateCell(c, angle);
      if (mirrored && !isFront) rc = mirrorCell(rc);
      return rc;
    });
  }

  function cellKey(x, y) { return x + ',' + y; }

  // Precompute every legal placement of every piece against the FULL board
  // (before any date-specific exclusion). Each placement is one specific
  // (angle,mirrored,A,B) with the resulting absolute cell list and its
  // corresponding (xPos,yPos) encoding.
  function allPlacements() {
    const board = boardCells();
    const boardSet = new Set(board.map(([x, y]) => cellKey(x, y)));
    const byPiece = {};
    for (const id of PCS_LIST) {
      const isFront = FRONT_PCS.has(id);
      const placements = [];
      for (const { angle, mirrored } of reachableOrientations(id)) {
        const shape = transformShape(id, angle, mirrored);
        const { xOfs, yOfs } = ofsFor(angle, mirrored, isFront);
        const xs = shape.map(c => c[0]), ys = shape.map(c => c[1]);
        // search anchors generously; board is only 7x8 so this stays tiny
        for (let A = -3; A <= 9; A++) {
          for (let B = -3; B <= 9; B++) {
            // A is tx/100 (pixel anchor / cell size); boardCells()'s cell g
            // covers pixel [100*(g+1), 100*(g+2)) (it accounts for
            // boardXcoord=100 the same way computePcsPos() does), while a
            // shape cell (cx,cy) translated by tx=100*A occupies pixel
            // [100*(cx+A), 100*(cx+A+1)) -- so the matching board index is
            // cx+A-1, not cx+A. Missing that -1 here validated every
            // placement one board cell off from where it actually renders.
            const absCells = shape.map(([cx, cy]) => [cx + A - 1, cy + B - 1]);
            if (absCells.every(([x, y]) => boardSet.has(cellKey(x, y)))) {
              const xPos = A - 1 + xOfs;
              const yPos = B - 1 + yOfs;
              if (xPos < 0 || xPos > 7 || yPos < 0 || yPos > 7) continue; // must fit the 3-bit encoding
              placements.push({ id, angle, mirrored, absCells, xPos, yPos });
            }
          }
        }
      }
      byPiece[id] = placements;
    }
    return { board, byPiece };
  }

  // --- exact-cover backtracking ---
  function solve(excludedCells, precomputed) {
    const { board, byPiece } = precomputed || allPlacements();
    const excludedSet = new Set(excludedCells.map(([x, y]) => cellKey(x, y)));
    const cells = board.filter(([x, y]) => !excludedSet.has(cellKey(x, y)));
    if (cells.length !== 48) return null; // sanity guard, shouldn't happen with valid inputs

    const cellIndex = new Map(cells.map(([x, y], i) => [cellKey(x, y), i]));
    // Index placements by the cell they cover, not just by piece -- the MRV
    // heuristic below needs "who covers cell i", and re-deriving that from
    // "all placements of all pieces" on every node is what made the first
    // cut of this heuristic slower than the naive version it replaced.
    const cellToPlacements = cells.map(() => []);
    for (const id of PCS_LIST) {
      for (const p of byPiece[id]) {
        let mask = 0n, ok = true;
        for (const [x, y] of p.absCells) {
          const idx = cellIndex.get(cellKey(x, y));
          if (idx === undefined) { ok = false; break; }
          mask |= (1n << BigInt(idx));
        }
        if (!ok) continue;
        const placement = { ...p, mask };
        for (const [x, y] of p.absCells) {
          cellToPlacements[cellIndex.get(cellKey(x, y))].push(placement);
        }
      }
    }

    const fullMask = (1n << BigInt(cells.length)) - 1n;
    const chosen = {};

    // Minimum-remaining-values heuristic: always branch on the uncovered
    // cell with the *fewest* legal covering placements left. A cell with
    // zero options is an immediate dead end, so this also gives near-instant
    // pruning on unsolvable inputs instead of exhausting the whole tree.
    function backtrack(usedMask, remainingSet) {
      if (usedMask === fullMask) return true;

      let bestOptions = null;
      for (let i = 0; i < cells.length; i++) {
        if ((usedMask >> BigInt(i)) & 1n) continue;
        const options = [];
        for (const p of cellToPlacements[i]) {
          if (remainingSet.has(p.id) && !(p.mask & usedMask)) options.push(p);
        }
        if (options.length === 0) return false; // this cell can never be covered -> dead branch
        if (bestOptions === null || options.length < bestOptions.length) {
          bestOptions = options;
          if (options.length === 1) break; // can't beat a forced move
        }
      }

      for (const p of bestOptions) {
        chosen[p.id] = p;
        remainingSet.delete(p.id);
        if (backtrack(usedMask | p.mask, remainingSet)) return true;
        remainingSet.add(p.id);
        delete chosen[p.id];
      }
      return false;
    }

    const found = backtrack(0n, new Set(PCS_LIST));
    return found ? { ...chosen } : null;
  }

  // --- hex encoding, matching getHexPcsPos()/placePieces() in script.js ---
  const NB_ASYM_PCS = 7; // pcsList[0..6] are the non-front (mirrorable) pieces

  function encodeSolution(solutionByPiece) {
    let hex = "";
    for (const id of PCS_LIST) {
      const p = solutionByPiece[id];
      // getHexPcsPos() (script.js) packs the *mirror-adjusted* angle into the
      // rotation bits, not the raw visual angle -- see the `pcsAngle = (360 -
      // pcsAngle) % 360` step it applies for mirrored, non-front pieces
      // before computing rotCode. placePieces() undoes the same adjustment
      // on decode, so both sides must agree on it or the piece rotates/lands
      // 180deg off from where it's supposed to (only visible for mirrored,
      // non-front pieces at a 90/270 visual angle -- 0 and 180 are fixed
      // points of this transform, which is why it's easy to miss).
      let byteAngle = p.angle;
      if (p.mirrored && !FRONT_PCS.has(id)) {
        byteAngle = (360 - byteAngle) % 360;
      }
      const rotCode = (4 - Math.trunc(byteAngle / 90)) % 4;
      const pcsPos = p.xPos + (p.yPos * 8) + (rotCode * 64);
      hex += pcsPos.toString(16).padStart(2, "0");
    }
    let sideByte = 0;
    for (let j = 0; j < NB_ASYM_PCS; j++) {
      const id = PCS_LIST[j];
      if (solutionByPiece[id].mirrored) sideByte += 2 ** j;
    }
    hex += sideByte.toString(16).padStart(2, "0");
    return hex;
  }

  // Exclusion-cell positions, matching updSquaresPos() in script.js.
  function excludedCellsFor(maasaNum, nakshatraNum, raashiNum) {
    return [
      [maasaNum % 6, Math.floor(maasaNum / 6)],           // monthSquare
      [nakshatraNum % 7, Math.floor(nakshatraNum / 7) + 2], // daySquare
      [raashiNum % 6, Math.floor(raashiNum / 6) + 6],       // weekdaySquare
    ];
  }

  function solvePanchang(maasaNum, nakshatraNum, raashiNum, precomputed) {
    const excluded = excludedCellsFor(maasaNum, nakshatraNum, raashiNum);
    const solution = solve(excluded, precomputed);
    return solution ? encodeSolution(solution) : null;
  }

  const api = {
    PCS_LIST, FRONT_PCS, SYM_PCS, BASE_SHAPES,
    boardCells, rotateCell, mirrorCell, transformShape, reachableOrientations,
    allPlacements, solve, encodeSolution, excludedCellsFor, solvePanchang,
  };

  if (typeof module !== "undefined" && module.exports) {
    module.exports = api;
  } else {
    root.PanchangSolver = api;
  }
})(typeof window !== "undefined" ? window : globalThis);
