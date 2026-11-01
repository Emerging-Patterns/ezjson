# proofs of laws/FixedWritesDigits.bend
import Base
import ../src/fixed.bend as F
import ../laws/FixedWritesDigits.bend as Laws

def Laws.write_parts(_nn, _digits):
  {==}

def Laws.point_none(_int, _frac):
  {==}

def Laws.point_some(_mm, _int, _frac):
  {==}

def Laws.trim_zero(_tl):
  {==}

def Laws.trim_lead(ch, tl, h):
  %Equal.sym(Bool, Char.is_eq(ch, '0'), False{}, h)
    : {F.trim.at(_, ch, tl, _u => F.trim(tl)) == SCon{ch, tl} : String}
  {==}

def Laws.trim_zeros(kk):
  match kk:
    case 0n:
      {==}
    case 1n+jj:
      Laws.trim_zeros(jj)
