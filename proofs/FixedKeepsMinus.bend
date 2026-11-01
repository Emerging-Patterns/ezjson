# proofs of laws/FixedKeepsMinus.bend
import Base
import ../src/fixed.bend as F
import ../laws/FixedKeepsMinus.bend as Laws

def Laws.text_minus(_txt, _nn):
  {==}

def Laws.text_plain(ch, tl, nn, h):
  %Equal.sym(Bool, Char.is_eq(ch, '-'), False{}, h)
    : {F.text.at(_, ch, tl, nn) == F.unsigned(SCon{ch, tl}, nn) : String}
  {==}

def Laws.text_empty(_nn):
  {==}
