# proofs of laws/SkipPassesOneValue.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/pull.bend as Pull
import ../laws/SkipPassesOneValue.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1
import ./lemmas/NatArithmetic.bend as M2
import ./lemmas/WordArithmetic.bend as M3

# laws/SkipPassesOneValue.bend: skip drops one whole value

# a walk's answer, or the walk resumed with `ff` more jumps
def obind(oo: Pull.Out, ff: Nat) -> Pull.Out:
  match oo:
    case Pull.Fin{got}:
      Pull.Fin{got}
    case Pull.More{txt, st}:
      Pull.next.go(ff, txt, st)

# a finished step returns its answer on any budget
law go_md:
  for +ff: Nat
  for +txt: String
  for stop: Pull.Stop
  for saved: String
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(ff, txt, Pull.S{Pull.MDone{stop, saved}, stack, goal, done, bad})
    == Pull.Fin{(stop, Pull.Cur{saved, stack, done, bad})} : Pull.Out}

def go_md(ff, txt, _stop, _saved, _stack, _goal, _done, _bad):
  match ff txt:
    case 0n SNil{}:
      {==}
    case 0n SCon{_, _}:
      {==}
    case 1n+_ SNil{}:
      {==}
    case 1n+_ SCon{_, _}:
      {==}

# a step that stopped on the suffix in hand returns it on any budget
law go_mr:
  for +ff: Nat
  for +txt: String
  for stop: Pull.Stop
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(ff, txt, Pull.S{Pull.MRest{stop}, stack, goal, done, bad})
    == Pull.Fin{(stop, Pull.Cur{txt, stack, done, bad})} : Pull.Out}

def go_mr(ff, txt, _stop, _stack, _goal, _done, _bad):
  match ff txt:
    case 0n SNil{}:
      {==}
    case 0n SCon{_, _}:
      {==}
    case 1n+_ SNil{}:
      {==}
    case 1n+_ SCon{_, _}:
      {==}

# a walk on a budget of aa + bb jumps is the walk on aa, resumed on bb
law go_add:
  for +aa: Nat
  for +xx: String
  for +st: Pull.St
  for +bb: Nat
  {Pull.next.go(Nat.add(aa, bb), xx, st) == obind(Pull.next.go(aa, xx, st), bb) : Pull.Out}

def go_add(aa, xx, st, bb):
  match aa xx st:
    case 0n SNil{} Pull.S{Pull.MIdle{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MIdle{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, False{}}:
      go_md(bb, SNil{}, stop, saved, stack, goal, done, False{})
    case 0n SNil{} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, True{}}:
      go_md(bb, SNil{}, stop, saved, stack, goal, done, True{})
    case 0n SNil{} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, False{}}:
      go_mr(bb, SNil{}, stop, stack, goal, done, False{})
    case 0n SNil{} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, True{}}:
      go_mr(bb, SNil{}, stop, stack, goal, done, True{})
    case 0n SNil{} Pull.S{Pull.MQuote{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MQuote{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SNil{} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, False{}}:
      go_md(bb, SCon{ch, tl}, stop, saved, stack, goal, done, False{})
    case 0n SCon{+ch, +tl} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, True{}}:
      go_md(bb, SCon{ch, tl}, stop, saved, stack, goal, done, True{})
    case 0n SCon{+ch, +tl} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, False{}}:
      go_mr(bb, SCon{ch, tl}, stop, stack, goal, done, False{})
    case 0n SCon{+ch, +tl} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, True{}}:
      go_mr(bb, SCon{ch, tl}, stop, stack, goal, done, True{})
    case 0n SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, +goal, +done, True{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, False{}}:
      {==}
    case 0n SCon{+ch, +tl} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, False{}}:
      go_add(pp, "", Pull.word.burst(SNil{}, buf, nn, num, stack, goal, False{}), bb)
    case 1n+pp SNil{} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, True{}}:
      go_add(pp, "", Pull.word.burst(SNil{}, buf, nn, num, stack, goal, True{}), bb)
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SNil{} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, False{}}:
      go_add(pp, rest, Pull.S{mode, stack, goal, done, False{}}, bb)
    case 1n+pp SNil{} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, True{}}:
      go_add(pp, rest, Pull.S{mode, stack, goal, done, True{}}, bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.look.plan(ch, stack, goal, done, Lex.classify(ch)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.err.st(goal), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, False{}}:
      go_add(pp, "", Pull.word.burst(SCon{ch, tl}, buf, nn, num, stack, goal, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+buf, +nn, +num}, +stack, +goal, +done, True{}}:
      go_add(pp, "", Pull.word.burst(SCon{ch, tl}, buf, nn, num, stack, goal, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.span.advance(Pull.span.kind.of(ch), cut, nn, stack, goal, done), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+cut, +nn}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.err.st(goal), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.copy.hit(ch, tl, buf, stack, goal, done, False{}, Lex.classify(ch),
        U32.is_lt(Char.to_u32(ch), 32)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.copy.hit(ch, tl, buf, stack, goal, done, True{}, Lex.classify(ch),
        U32.is_lt(Char.to_u32(ch), 32)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.esc.hit(ch, tl, buf, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.esc.hit(ch, tl, buf, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.uni.hit(ch, tl, left2, acc, buf, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+left2, +acc, +buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.uni.hit(ch, tl, left2, acc, buf, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.hi.hit(tl, hi, buf, stack, goal, done, False{}, Lex.classify(ch)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+hi, +buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.hi.hit(tl, hi, buf, stack, goal, done, True{}, Lex.classify(ch)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.hiesc.hit(ch, tl, hi, buf, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+hi, +buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.hiesc.hit(ch, tl, hi, buf, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.lo.hit(ch, tl, left2, acc, hi, buf, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+left2, +acc, +hi, +buf}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.lo.hit(ch, tl, left2, acc, hi, buf, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.advance(Pull.span.kind.of(ch), stack, goal, done), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.err.st(goal), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.esc(ch, tl, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.sk.esc(ch, tl, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.uni(ch, tl, left2, acc, stack, goal, done, False{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+left2, +acc}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.sk.uni(ch, tl, left2, acc, stack, goal, done, True{}), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.hi(stack, goal, done, hi, Lex.classify(ch)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+hi}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.sk.hi(stack, goal, done, hi, Lex.classify(ch)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.hiesc(stack, goal, done, hi, U32.is_eq(Char.to_u32(ch), 117)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+hi}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.sk.hiesc(stack, goal, done, hi, U32.is_eq(Char.to_u32(ch), 117)), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.sk.lo.go(ch, tl, left2, acc, hi, stack, goal, done, Lex.hex.ok(Char.to_u32(ch))), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+left2, +acc, +hi}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.sk.lo.go(ch, tl, left2, acc, hi, stack, goal, done, Lex.hex.ok(Char.to_u32(ch))), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, False{}}:
      {==}
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MRest{+stop}, +stack, +goal, +done, True{}}:
      {==}
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, +goal, +done, False{}}:
      go_add(1n+pp, tl, Pull.quote.first(ch, tl, stack, goal, done), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, +goal, +done, True{}}:
      go_add(1n+pp, tl, Pull.err.st(goal), bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, False{}}:
      go_add(pp, rest, Pull.S{mode, stack, goal, done, False{}}, bb)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+rest, +mode}, +stack, +goal, +done, True{}}:
      go_add(pp, rest, Pull.S{mode, stack, goal, done, True{}}, bb)

# a level of budget: 4 jumps at level 0, twice the level below otherwise
def rl(lvl: Nat) -> Nat:
  match lvl:
    case 0n:
      4n
    case 1n+(+pp):
      Nat.add(rl(pp), rl(pp))

# the budget of next.grow(1 + pp, lvl, _): levels lvl to lvl + pp
def cpl(pp: Nat, +lvl: Nat) -> Nat:
  match pp:
    case 0n:
      rl(lvl)
    case 1n+qq:
      Nat.add(rl(lvl), cpl(qq, 1n+lvl))

# a level runs the walk on its budget
law run_ob:
  for +lvl: Nat
  for oo: Pull.Out
  {Pull.next.run(lvl, oo) == obind(oo, rl(lvl)) : Pull.Out}

def run_ob(lvl, oo):
  match lvl oo:
    case 0n Pull.More{+txt, +st}:
      {==}
    case 1n+pp Pull.More{+txt, +st}:
      Equal.trans(Pull.Out, Pull.next.run(pp, Pull.next.run(pp, Pull.More{txt, st})),
        obind(Pull.next.run(pp, Pull.More{txt, st}), rl(pp)), Pull.next.go(Nat.add(rl(pp), rl(pp)), txt, st),
        run_ob(pp, Pull.next.run(pp, Pull.More{txt, st})),
        Equal.trans(Pull.Out, obind(Pull.next.run(pp, Pull.More{txt, st}), rl(pp)),
          obind(Pull.next.go(rl(pp), txt, st), rl(pp)), Pull.next.go(Nat.add(rl(pp), rl(pp)), txt, st),
          Equal.cong(Pull.Out, Pull.Out, zz => obind(zz, rl(pp)), Pull.next.run(pp, Pull.More{txt, st}),
            Pull.next.go(rl(pp), txt, st), run_ob(pp, Pull.More{txt, st})),
          Equal.sym(Pull.Out, Pull.next.go(Nat.add(rl(pp), rl(pp)), txt, st),
            obind(Pull.next.go(rl(pp), txt, st), rl(pp)), go_add(rl(pp), txt, st, rl(pp)))))
    case 0n Pull.Fin{_}:
      {==}
    case 1n+_ Pull.Fin{_}:
      {==}

# no levels left: the walk as it is
law grow0:
  for +lvl: Nat
  for oo: Pull.Out
  {Pull.next.grow(0n, lvl, oo) == oo : Pull.Out}

def grow0(_lvl, oo):
  match oo:
    case Pull.More{_, _}:
      {==}
    case Pull.Fin{_}:
      {==}

# levels lvl to lvl + pp run the walk on their budgets added
law grow_ob:
  for +pp: Nat
  for +lvl: Nat
  for oo: Pull.Out
  {Pull.next.grow(1n+pp, lvl, oo) == obind(oo, cpl(pp, lvl)) : Pull.Out}

def grow_ob(pp, lvl, oo):
  match pp oo:
    case 0n Pull.More{+txt, +st}:
      Equal.trans(Pull.Out, Pull.next.grow(0n, 1n+lvl, Pull.next.run(lvl, Pull.More{txt, st})),
        Pull.next.run(lvl, Pull.More{txt, st}), Pull.next.go(rl(lvl), txt, st),
        grow0(1n+lvl, Pull.next.run(lvl, Pull.More{txt, st})), run_ob(lvl, Pull.More{txt, st}))
    case 1n+qq Pull.More{+txt, +st}:
      Equal.trans(Pull.Out, Pull.next.grow(1n+qq, 1n+lvl, Pull.next.run(lvl, Pull.More{txt, st})),
        obind(Pull.next.run(lvl, Pull.More{txt, st}), cpl(qq, 1n+lvl)),
        Pull.next.go(Nat.add(rl(lvl), cpl(qq, 1n+lvl)), txt, st),
        grow_ob(qq, 1n+lvl, Pull.next.run(lvl, Pull.More{txt, st})),
        Equal.trans(Pull.Out, obind(Pull.next.run(lvl, Pull.More{txt, st}), cpl(qq, 1n+lvl)),
          obind(Pull.next.go(rl(lvl), txt, st), cpl(qq, 1n+lvl)),
          Pull.next.go(Nat.add(rl(lvl), cpl(qq, 1n+lvl)), txt, st),
          Equal.cong(Pull.Out, Pull.Out, zz => obind(zz, cpl(qq, 1n+lvl)), Pull.next.run(lvl, Pull.More{txt, st}),
            Pull.next.go(rl(lvl), txt, st), run_ob(lvl, Pull.More{txt, st})),
          Equal.sym(Pull.Out, Pull.next.go(Nat.add(rl(lvl), cpl(qq, 1n+lvl)), txt, st),
            obind(Pull.next.go(rl(lvl), txt, st), cpl(qq, 1n+lvl)), go_add(rl(lvl), txt, st, cpl(qq, 1n+lvl)))))
    case 0n Pull.Fin{_}:
      {==}
    case 1n+_ Pull.Fin{_}:
      {==}

# the whole budget of a walk, once uu is known. The checker expands a closed
# Nat to compare it, and this one is about 2^35, so it is named through uu
def cplu(lvl: Nat, pp: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      cpl(pp, lvl)

# grow_ob, with the budget named through uu
law grow_obu:
  for +pp: Nat
  for +lvl: Nat
  for oo: Pull.Out
  for +uu: Unit
  {Pull.next.grow(1n+pp, lvl, oo) == obind(oo, cplu(lvl, pp, uu)) : Pull.Out}

def grow_obu(pp, lvl, oo, uu):
  match uu:
    case Unit{}:
      grow_ob(pp, lvl, oo)

# a walk is one run of go on the whole budget
law walk_ob:
  for +txt: String
  for +st: Pull.St
  for +uu: Unit
  {Pull.next.walk(txt, st) == Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), txt, st)) : (Pull.Stop & Pull.Cur)}

def walk_ob(txt, st, uu):
  Equal.cong(Pull.Out, (Pull.Stop & Pull.Cur), zz => Pull.next.fin(zz), Pull.next.grow(1n+32n, 0n, Pull.More{txt, st}),
    Pull.next.go(cplu(0n, 32n, uu), txt, st), grow_obu(32n, 0n, Pull.More{txt, st}, uu))

# twice the characters of a text, on top of acc: the jumps a skip over it may
# take, two for each word, and each word at least one character
def fu(txt: String, acc: Nat) -> Nat:
  match txt:
    case SNil{}:
      acc
    case SCon{_, tl}:
      fu(tl, 2n+acc)

# one more on top is one more
law fu_s:
  for +txt: String
  for +acc: Nat
  {fu(txt, 1n+acc) == 1n+fu(txt, acc) : Nat}

def fu_s(txt, acc):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, +tl}:
      fu_s(tl, 2n+acc)

# laws/SkipPassesOneValue.bend: a reader and a skip from the same place

# a level of budget, less one
def rlm(lvl: Nat) -> Nat:
  match lvl:
    case 0n:
      3n
    case 1n+(+pp):
      Nat.add(rlm(pp), rl(pp))

# a level of budget is at least one jump
law rl_s:
  for +lvl: Nat
  {rl(lvl) == 1n+rlm(lvl) : Nat}

def rl_s(lvl):
  match lvl:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, zz => Nat.add(zz, rl(pp)), rl(pp), 1n+rlm(pp), rl_s(pp))

# the budget of levels, less one
def cplm(pp: Nat, +lvl: Nat) -> Nat:
  match pp:
    case 0n:
      rlm(lvl)
    case 1n+qq:
      Nat.add(rlm(lvl), cpl(qq, 1n+lvl))

# the budget of levels is at least one jump
law cpl_s:
  for +pp: Nat
  for +lvl: Nat
  {cpl(pp, lvl) == 1n+cplm(pp, lvl) : Nat}

def cpl_s(pp, lvl):
  match pp:
    case 0n:
      rl_s(lvl)
    case 1n+(+qq):
      Equal.cong(Nat, Nat, zz => Nat.add(zz, cpl(qq, 1n+lvl)), rl(lvl), 1n+rlm(lvl), rl_s(lvl))

# the whole budget less one, once uu is known
def cplmu(lvl: Nat, pp: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      cplm(pp, lvl)

# the whole budget is at least one jump
law cplu_s:
  for +lvl: Nat
  for +pp: Nat
  for +uu: Unit
  {cplu(lvl, pp, uu) == 1n+cplmu(lvl, pp, uu) : Nat}

def cplu_s(lvl, pp, uu):
  match uu:
    case Unit{}:
      cpl_s(pp, lvl)

# next is one run of go on the whole budget
law next_ob:
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +uu: Unit
  {Ezjson.next(Pull.Cur{rest, stack, done, False{}})
    == Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), rest,
      Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}))) : (Pull.Ev & Pull.Cur)}

def next_ob(rest, stack, done, uu):
  Equal.trans((Pull.Ev & Pull.Cur), Pull.next.use(Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done,
    False{}})), Pull.next.use(Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), rest, Pull.S{Pull.MIdle{}, stack,
    Pull.GNext{}, done, False{}}))), Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), rest,
    Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}))),
    Equal.cong((Pull.Stop & Pull.Cur), (Pull.Ev & Pull.Cur), zz => Pull.next.use(zz),
      Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}),
      Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}})),
      walk_ob(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}, uu)),
    Equal.cong(Nat, (Pull.Ev & Pull.Cur), zz => Pull.next.use(Pull.next.fin(Pull.next.go(zz, rest,
      Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}))), cplu(0n, 32n, uu), 1n+cplmu(0n, 32n, uu),
      cplu_s(0n, 32n, uu)))

# skip on a live cursor is one run of go on the whole budget
law skip_ob:
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +uu: Unit
  {Ezjson.skip(Pull.Cur{rest, stack, False{}, False{}})
    == Pull.skip.use(Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), rest,
      Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}))) : Pull.Cur}

def skip_ob(rest, stack, uu):
  Equal.cong((Pull.Stop & Pull.Cur), Pull.Cur, zz => Pull.skip.use(zz),
    Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), rest, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{},
      False{}})), walk_ob(rest, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}, uu))

# a failed or ended step, or a budget used up: what a reader whose root is
# over gets
def dto.g(got: (Pull.Stop & Pull.Cur)) -> Type:
  match got:
    case (Pull.SEv{Pull.EErr{}}, _):
      Unit
    case (Pull.SEv{Pull.EEnd{}}, _):
      Unit
    case _:
      Empty

# dto.g, on a walk's result
def dto(oo: Pull.Out) -> Type:
  match oo:
    case Pull.More{_, _}:
      Unit
    case Pull.Fin{got}:
      dto.g(got)

# a failed step is one dto allows
law dto_err:
  for +fn: Nat
  for +tl: String
  for +goal: Pull.Goal
  dto(Pull.next.go(1n+fn, tl, Pull.err.st(goal)))

def dto_err(_fn, tl, _goal):
  match tl:
    case SNil{}:
      Unit{}
    case SCon{_, _}:
      Unit{}

# the character after a finished root, whatever it is
law dt_plan:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +cls: Lex.Class
  for ih: dto(Pull.next.go(1n+fn, tl, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, True{}, False{}}))
  dto(Pull.next.go(1n+fn, tl, Pull.look.plan(ch, stack, Pull.GNext{}, True{}, cls)))

def dt_plan(tl, fn, _ch, _stack, cls, ih):
  match cls:
    case Lex.CSpace{}:
      ih
    case Lex.CPunct{_}:
      dto_err(fn, tl, Pull.GNext{})
    case Lex.CQuote{}:
      dto_err(fn, tl, Pull.GNext{})
    case Lex.CBack{}:
      dto_err(fn, tl, Pull.GNext{})
    case Lex.COther{}:
      dto_err(fn, tl, Pull.GNext{})

# a reader whose root is over fails or ends
law dt_go:
  for +xx: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  dto(Pull.next.go(1n+fn, xx, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, True{}, False{}}))

def dt_go(xx, fn, stack):
  match xx:
    case SNil{}:
      Unit{}
    case SCon{+ch, +tl}:
      dt_plan(tl, fn, ch, stack, Lex.classify(ch), dt_go(tl, fn, stack))

# a failed or ended step starts no value
law dto_len:
  for oo: Pull.Out
  for +es: List<&2, D1.Evt>
  for +dd: Nat
  for hh: dto(oo)
  {Laws.val_len(D1.view(D1.ev_of(Pull.next.use(Pull.next.fin(oo)))) <> es, dd) == None{}
    : Maybe<&2, Nat>}

def dto_len(oo, es, dd, hh):
  match oo:
    case Pull.More{_, _}:
      {==}
    case Pull.Fin{(Pull.SEv{Pull.EErr{}}, _)}:
      {==}
    case Pull.Fin{(Pull.SEv{Pull.EEnd{}}, _)}:
      {==}
    case Pull.Fin{(Pull.SEv{Pull.ENull{}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.ENull{}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EBool{+bb}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EBool{bb}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.ENum{+s1, +n1}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.ENum{s1, n1}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EStr{+s1}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EStr{s1}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EStrS{+s1, +n1}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EStrS{s1, n1}}, cc)))) <> es,
        dd) == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EKey{+s1}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EKey{s1}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EKeyS{+s1, +n1}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EKeyS{s1, n1}}, cc)))) <> es,
        dd) == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EBeginArr{}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EEndArr{}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EBeginObj{}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, +cc)}:
      Empty.absurd({Laws.val_len(D1.view(D1.ev_of(Pull.next.use((Pull.SEv{Pull.EEndObj{}}, cc)))) <> es, dd)
        == None{} : Maybe<&2, Nat>}, hh)
    case Pull.Fin{(Pull.SSkip{}, _)}:
      {==}

# a skip's walk resumed at depth dd from the cursor a reader's event left,
# on some budget over its text. Past the root nothing is claimed
def kr.on(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool, dd: Nat) -> Type:
  match dn:
    case True{}:
      Unit
    case False{}:
      &gg: Nat -> {os == Pull.next.go(1n+fu(rr, gg), rr, Pull.S{Pull.MIdle{}, st, Pull.GSkip{dd}, False{}, False{}})
        : Pull.Out}

# a skip that has dropped the value, with the cursor the reader's event left
def kr.fin(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool) -> Type:
  {os == Pull.Fin{(Pull.SSkip{}, Pull.Cur{rr, st, dn, False{}})} : Pull.Out}

# after a scalar
def kr.v(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool, dd: Nat) -> Type:
  match dd:
    case 0n:
      kr.fin(os, rr, st, dn)
    case 1n+kk:
      kr.on(os, rr, st, dn, 1n+kk)

# after a key
def kr.k(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool, dd: Nat) -> Type:
  match dd:
    case 0n:
      Unit
    case 1n+kk:
      kr.on(os, rr, st, dn, 1n+kk)

# after a container's begin
def kr.b(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool, dd: Nat) -> Type:
  kr.on(os, rr, st, dn, 1n+dd)

# after a container's end
def kr.n(os: Pull.Out, rr: String, st: List<&2, Pull.Frame>, dn: Bool, dd: Nat) -> Type:
  match dd:
    case 0n:
      Unit
    case 1n+kk:
      match kk:
        case 0n:
          kr.fin(os, rr, st, dn)
        case 1n+jj:
          kr.on(os, rr, st, dn, 1n+jj)

# what a skip at depth dd must be, after a reader's event from the same place
def kr.e(ev: Pull.Ev, cur: Pull.Cur, os: Pull.Out, dd: Nat) -> Type:
  match ev:
    case Pull.EErr{}:
      Unit
    case Pull.EEnd{}:
      Unit
    case Pull.ENull{}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.v(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EBool{_}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.v(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.ENum{_, _}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.v(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EStr{_}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.v(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EStrS{_, _}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.v(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EKey{_}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.k(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EKeyS{_, _}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.k(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EBeginArr{}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.b(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EBeginObj{}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.b(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EEndArr{}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.n(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EEndObj{}:
      match cur:
        case Pull.Cur{rr, st, dn, False{}}:
          kr.n(os, rr, st, dn, dd)
        case Pull.Cur{_, _, _, True{}}:
          Empty

# kr.e, on a finished step
def kr.g(got: (Pull.Stop & Pull.Cur), os: Pull.Out, dd: Nat) -> Type:
  match got:
    case (Pull.SEv{ev}, cur):
      kr.e(ev, cur, os, dd)
    case (Pull.SSkip{}, _):
      Unit

# a reader's walk and a skip's walk at depth dd from the same place: a
# budget the reader used up claims nothing
def kr(on: Pull.Out, os: Pull.Out, dd: Nat) -> Type:
  match on:
    case Pull.More{_, _}:
      Unit
    case Pull.Fin{got}:
      kr.g(got, os, dd)

# laws/SkipPassesOneValue.bend: a string closed on the suffix in hand, or one already past

# a reader's string placed on the suffix in hand, or on that suffix given
law ph:
  for +fn: Nat
  for +tl: String
  for +pc: Pull.Piece
  for +stack: List<&2, Pull.Frame>
  {Pull.next.go(1n+fn, tl, Pull.str.place.here(pc, stack, Pull.GNext{}))
    == Pull.next.go(1n+fn, tl, Pull.str.place(pc, tl, stack, Pull.GNext{})) : Pull.Out}

def ph(_fn, tl, _pc, stack):
  match tl stack:
    case SNil{} Nil{}:
      {==}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames}:
      {==}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Nil{}:
      {==}
    case SCon{_, _} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames}:
      {==}
    case SCon{_, _} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames}:
      {==}

# a reader not starting a value: it fails, ends, reads a key, or runs out
def kim.e(ev: Pull.Ev, cur: Pull.Cur) -> Type:
  match ev:
    case Pull.EErr{}:
      Unit
    case Pull.EEnd{}:
      Unit
    case Pull.EKey{_}:
      match cur:
        case Pull.Cur{_, _, _, False{}}:
          Unit
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case Pull.EKeyS{_, _}:
      match cur:
        case Pull.Cur{_, _, _, False{}}:
          Unit
        case Pull.Cur{_, _, _, True{}}:
          Empty
    case _:
      Empty

# kim.e, on a finished step
def kim.g(got: (Pull.Stop & Pull.Cur)) -> Type:
  match got:
    case (Pull.SEv{ev}, cur):
      kim.e(ev, cur)
    case (Pull.SSkip{}, _):
      Unit

# kim.e, on a walk
def kim(on: Pull.Out) -> Type:
  match on:
    case Pull.More{_, _}:
      Unit
    case Pull.Fin{got}:
      kim.g(got)

# an open object waits for a key
def keytop(stack: List<&2, Pull.Frame>) -> Bool:
  match stack:
    case Con{Pull.FObj{Pull.SKey{}, _}, _}:
      True{}
    case _:
      False{}

# where the relation kq may be asked for
def selok(sel: Bool, stack: List<&2, Pull.Frame>) -> Bool:
  match sel:
    case True{}:
      True{}
    case False{}:
      keytop(stack)

# a reader not starting a value is in step with a failed skip at depth 0
law kim_kr:
  for on: Pull.Out
  for os: Pull.Out
  for hh: kim(on)
  kr(on, os, 0n)

def kim_kr(on, os, hh):
  match on:
    case Pull.More{_, _}:
      Unit{}
    case Pull.Fin{(Pull.SSkip{}, _)}:
      Unit{}
    case Pull.Fin{(Pull.SEv{Pull.EErr{}}, _)}:
      Unit{}
    case Pull.Fin{(Pull.SEv{Pull.EEnd{}}, _)}:
      Unit{}
    case Pull.Fin{(Pull.SEv{Pull.EKey{+k1}}, Pull.Cur{+c1, +c2, +c3, True{}})}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EKey{k1}}, Pull.Cur{c1, c2, c3, True{}})}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EKey{_}}, Pull.Cur{_, _, _, False{}})}:
      Unit{}
    case Pull.Fin{(Pull.SEv{Pull.EKeyS{+k1, +k2}}, Pull.Cur{+c1, +c2, +c3, True{}})}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EKeyS{k1, k2}}, Pull.Cur{c1, c2, c3, True{}})}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EKeyS{_, _}}, Pull.Cur{_, _, _, False{}})}:
      Unit{}
    case Pull.Fin{(Pull.SEv{Pull.ENull{}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.ENull{}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EBool{+k1}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EBool{k1}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.ENum{+k1, +k2}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.ENum{k1, k2}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EStr{+k1}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EStr{k1}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EStrS{+k1, +k2}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EStrS{k1, k2}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, cc)}, os, 0n), hh)
    case Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, +cc)}:
      Empty.absurd(kr(Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, cc)}, os, 0n), hh)

# the reader's relation to a skip in a string: kr, or, for a key where the
# skip at depth 0 has already failed, that the reader does not start a value
def kq(sel: Bool, on: Pull.Out, os: Pull.Out, ee: Nat) -> Type:
  match sel:
    case True{}:
      kr(on, os, ee)
    case False{}:
      kim(on)

# a string closed for both: in step
law se:
  for +sel: Bool
  for +fn: Nat
  for +tl: String
  for +pn: Pull.Piece
  for +ps: Pull.Piece
  for +g2: Nat
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +hsel: {selok(sel, stack) == True{} : Bool}
  kq(sel, Pull.next.go(1n+fn, tl, Pull.str.place.here(pn, stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, g2), tl, Pull.str.place.here(ps, stack, Pull.GSkip{ee})), ee)

def se(sel, fn, tl, pn, ps, g2, stack, ee, hsel):
  match sel tl pn stack ee:
    case True{} SNil{} Pull.PSpan{+p1, +p2} Nil{} 0n:
      {==}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Nil{} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Nil{} 0n:
      {==}
    case True{} SNil{} Pull.POwn{+p1} Nil{} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Nil{} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Nil{} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Nil{} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Nil{} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      {==}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      (g2, {==})
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      Unit{}
    case True{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      Unit{}
    case False{} SNil{} Pull.PSpan{+p1, +p2} Nil{} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Nil{} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Nil{} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Nil{} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Nil{} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Nil{} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{1n+kk})), 1n+kk),
        hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Nil{} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Nil{} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Nil{}, Pull.GNext{})),
        Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps, Nil{}, Pull.GSkip{1n+kk})), 1n+kk),
        hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SVal{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SVal{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCom{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCom{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SKey{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SKey{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SKey{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SKey{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SKey{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SKey{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SKey{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SKey{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FArr{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCol{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCol{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FArr{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FArr{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FArr{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SVal{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SVal{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SVal{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SVal{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SVal{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCom{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCom{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCom{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCom{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCom{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 0n:
      Unit{}
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SKey{}, +fr}, +frames} 1n+kk:
      Unit{}
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.PSpan{p1, p2}, Con{Pull.FObj{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCol{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SNil{} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SNil{}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCol{}, fr},
        frames}, Pull.GNext{})), Pull.next.go(1n+fu(SNil{}, g2), SNil{}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.PSpan{+p1, +p2} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.PSpan{p1, p2},
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1},
        Pull.str.place.here(ps, Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 0n:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{0n})), 0n), hsel)
    case False{} SCon{+c1, +t1} Pull.POwn{+p1} Con{Pull.FObj{Pull.SCol{}, +fr}, +frames} 1n+kk:
      M1.no(kq(False{}, Pull.next.go(1n+fn, SCon{c1, t1}, Pull.str.place.here(Pull.POwn{p1}, Con{Pull.FObj{Pull.SCol{},
        fr}, frames}, Pull.GNext{})), Pull.next.go(1n+fu(SCon{c1, t1}, g2), SCon{c1, t1}, Pull.str.place.here(ps,
        Con{Pull.FObj{Pull.SCol{}, fr}, frames}, Pull.GSkip{1n+kk})), 1n+kk), hsel)

# laws/SkipPassesOneValue.bend: a reader and a skip in step through a string

# the skip's string mode that goes with a reader's
def skm(mn: Pull.Mode) -> Pull.Mode:
  match mn:
    case Pull.MQuote{}:
      Pull.MQuote{}
    case Pull.MSpan{cut, nn}:
      Pull.MSpan{cut, nn}
    case Pull.MCopy{_}:
      Pull.MSkStr{}
    case Pull.MEsc{_}:
      Pull.MSkEsc{}
    case Pull.MUni{left2, acc, _}:
      Pull.MSkUni{left2, acc}
    case Pull.MHi{hi, _}:
      Pull.MSkHi{hi}
    case Pull.MHiEsc{hi, _}:
      Pull.MSkHiEsc{hi}
    case Pull.MLo{left2, acc, hi, _}:
      Pull.MSkLo{left2, acc, hi}
    case _:
      Pull.MIdle{}

# a reader's mode inside a string
def isstr(mn: Pull.Mode) -> Bool:
  match mn:
    case Pull.MQuote{}:
      True{}
    case Pull.MSpan{_, _}:
      True{}
    case Pull.MCopy{_}:
      True{}
    case Pull.MEsc{_}:
      True{}
    case Pull.MUni{_, _, _}:
      True{}
    case Pull.MHi{_, _}:
      True{}
    case Pull.MHiEsc{_, _}:
      True{}
    case Pull.MLo{_, _, _, _}:
      True{}
    case _:
      False{}

# a failed step of both
law kq_err:
  for +sel: Bool
  for +fn: Nat
  for +tl: String
  for +g2: Nat
  for +ee: Nat
  kq(sel, Pull.next.go(1n+fn, tl, Pull.err.st(Pull.GNext{})), Pull.next.go(1n+fu(tl, g2), tl,
    Pull.err.st(Pull.GSkip{ee})),
    ee)

def kq_err(sel, _fn, tl, _g2, _ee):
  match sel tl:
    case True{} SNil{}:
      Unit{}
    case True{} SCon{_, _}:
      Unit{}
    case False{} SNil{}:
      Unit{}
    case False{} SCon{_, _}:
      Unit{}

# a string that runs out, for both
law kq_bad:
  for +sel: Bool
  for +ee: Nat
  kq(sel, Pull.Fin{Pull.bad.cur()}, Pull.Fin{Pull.bad.cur()}, ee)

def kq_bad(sel, _ee):
  match sel:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the first character of a string, both in step
law ls_q:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +key: Pull.Skind
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.quote.go(key, ch, tl, stack, Pull.GNext{}, False{})), Pull.next.go(1n+fu(tl,
    2n+gg), tl, Pull.quote.go(key, ch, tl, stack, Pull.GSkip{ee}, False{})), ee)

def ls_q(tl, fn, ch, key, stack, ee, gg, sel, hsel, ih):
  match key:
    case Pull.KGo{}:
      ih(Pull.MSpan{SCon{ch, tl}, 1}, 2n+gg, {==})
    case Pull.KEnd{}:
      se(sel, fn, tl, Pull.PSpan{"", 0}, Pull.PSpan{"", 0}, 2n+gg, stack, ee, hsel)
    case Pull.KEsc{}:
      ih(Pull.MEsc{Pull.copy.rev("", 0, U32.is_zero(0), [])}, 2n+gg, {==})
    case Pull.KBad{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# one character of a span, both in step
law ls_sp:
  for +tl: String
  for +fn: Nat
  for +cut: String
  for +nn: U32
  for +key: Pull.Skind
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.span.advance(key, cut, nn, stack, Pull.GNext{}, False{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.span.advance(key, cut, nn, stack, Pull.GSkip{ee}, False{})), ee)

def ls_sp(tl, fn, cut, nn, key, stack, ee, gg, sel, hsel, ih):
  match key:
    case Pull.KGo{}:
      ih(Pull.MSpan{cut, U32.add(nn, 1)}, 2n+gg, {==})
    case Pull.KEnd{}:
      se(sel, fn, tl, Pull.PSpan{cut, nn}, Pull.PSpan{cut, nn}, 2n+gg, stack, ee, hsel)
    case Pull.KEsc{}:
      ih(Pull.MEsc{Pull.copy.rev(cut, nn, U32.is_zero(nn), [])}, 2n+gg, {==})
    case Pull.KBad{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# a reader's decoded string closes where the skip's does
law ls_cq:
  for +tl: String
  for +fn: Nat
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  kq(sel, Pull.next.go(1n+fn, tl, Pull.str.place(Pull.POwn{Lex.text(buf)}, tl, stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.str.skip.here(stack, Pull.GSkip{ee})), ee)

def ls_cq(tl, fn, buf, stack, ee, gg, sel, hsel):
  e = ph(fn, tl, Pull.POwn{Lex.text(buf)}, stack)
  %e : kq(sel, _, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.str.skip.here(stack, Pull.GSkip{ee})), ee)
  se(sel, fn, tl, Pull.POwn{Lex.text(buf)}, Pull.POwn{""}, 2n+gg, stack, ee, hsel)

# one character of a decoded string, both in step
law ls_cp:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +buf: List<&2, Char>
  for +cls: Lex.Class
  for +ctrl: Bool
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.copy.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, cls, ctrl)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.advance(Pull.span.kind(cls, ctrl), stack, Pull.GSkip{ee}, False{})), ee)

def ls_cp(tl, fn, ch, buf, cls, ctrl, stack, ee, gg, sel, hsel, ih):
  match cls ctrl:
    case Lex.CQuote{} True{}:
      ls_cq(tl, fn, buf, stack, ee, gg, sel, hsel)
    case Lex.CQuote{} False{}:
      ls_cq(tl, fn, buf, stack, ee, gg, sel, hsel)
    case Lex.CBack{} True{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.CBack{} False{}:
      ih(Pull.MEsc{buf}, 2n+gg, {==})
    case Lex.CSpace{} True{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.CSpace{} False{}:
      ih(Pull.MCopy{ch <> buf}, 2n+gg, {==})
    case Lex.COther{} True{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.COther{} False{}:
      ih(Pull.MCopy{ch <> buf}, 2n+gg, {==})
    case Lex.CPunct{+tok} True{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.CPunct{+tok} False{}:
      ih(Pull.MCopy{ch <> buf}, 2n+gg, {==})

# a short escape, both in step
law ls_eput:
  for +tl: String
  for +fn: Nat
  for +buf: List<&2, Char>
  for +got: Maybe<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.esc.put(tl, buf, stack, Pull.GNext{}, False{}, got)), Pull.next.go(1n+fu(tl,
    2n+gg), tl, Pull.sk.esc.put(tl, stack, Pull.GSkip{ee}, False{}, got)), ee)

def ls_eput(tl, fn, buf, got, _stack, ee, gg, sel, _hsel, ih):
  match got:
    case Some{+cc}:
      ih(Pull.MCopy{cc <> buf}, 2n+gg, {==})
    case None{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# the character after a backslash, both in step
law ls_es:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +buf: List<&2, Char>
  for +isu: Bool
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.esc.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, isu)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.esc.go(ch, tl, stack, Pull.GSkip{ee}, False{}, isu)), ee)

def ls_es(tl, fn, ch, buf, isu, stack, ee, gg, sel, hsel, ih):
  match isu:
    case True{}:
      ih(Pull.MUni{3n, 0, buf}, 2n+gg, {==})
    case False{}:
      ls_eput(tl, fn, buf, Lex.unescape(ch), stack, ee, gg, sel, hsel, ih)

# four hex digits are in, both in step
law ls_ue:
  for +tl: String
  for +fn: Nat
  for +cp: U32
  for +buf: List<&2, Char>
  for +sur: Lex.Sur
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.uni.end.go(tl, cp, buf, stack, Pull.GNext{}, False{}, sur)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.uni.end.go(tl, stack, Pull.GSkip{ee}, False{}, sur, cp)), ee)

def ls_ue(tl, fn, cp, buf, sur, _stack, ee, gg, sel, _hsel, ih):
  match sur:
    case Lex.SOk{}:
      ih(Pull.MCopy{Char.from_u32(cp) <> buf}, 2n+gg, {==})
    case Lex.SHi{}:
      ih(Pull.MHi{cp, buf}, 2n+gg, {==})
    case Lex.SLo{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# one more hex digit, both in step
law ls_up:
  for +tl: String
  for +fn: Nat
  for +left2: Nat
  for +acc: U32
  for +dig: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.uni.put(tl, left2, acc, dig, buf, stack, Pull.GNext{}, False{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.uni.put(tl, left2, acc, dig, stack, Pull.GSkip{ee}, False{})), ee)

def ls_up(tl, fn, left2, acc, dig, buf, stack, ee, gg, sel, hsel, ih):
  match left2:
    case 0n:
      ls_ue(tl, fn, (acc * 16 + dig : U32), buf, Lex.unicode.sur((acc * 16 + dig : U32)), stack, ee, gg, sel, hsel, ih)
    case 1n+pp:
      ih(Pull.MUni{pp, (acc * 16 + dig : U32), buf}, 2n+gg, {==})

# one hex digit of a \\u escape, both in step
law ls_uh:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +left2: Nat
  for +acc: U32
  for +buf: List<&2, Char>
  for +ok: Bool
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.uni.hit.go(ch, tl, left2, acc, buf, stack, Pull.GNext{}, False{}, ok)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.uni.go(ch, tl, left2, acc, stack, Pull.GSkip{ee}, False{}, ok)), ee)

def ls_uh(tl, fn, ch, left2, acc, buf, ok, stack, ee, gg, sel, hsel, ih):
  match ok:
    case True{}:
      ls_up(tl, fn, left2, acc, Lex.hex(ch), buf, stack, ee, gg, sel, hsel, ih)
    case False{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# the character after a high surrogate, both in step
law ls_hi:
  for +tl: String
  for +fn: Nat
  for +hi: U32
  for +buf: List<&2, Char>
  for +cls: Lex.Class
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.hi.hit.go(tl, hi, buf, stack, Pull.GNext{}, False{}, cls)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.hi(stack, Pull.GSkip{ee}, False{}, hi, cls)), ee)

def ls_hi(tl, fn, hi, buf, cls, _stack, ee, gg, sel, _hsel, ih):
  match cls:
    case Lex.CQuote{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.CBack{}:
      ih(Pull.MHiEsc{hi, buf}, 2n+gg, {==})
    case Lex.CSpace{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.COther{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.CPunct{_}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# the character after the backslash of a pair, both in step
law ls_he:
  for +tl: String
  for +fn: Nat
  for +hi: U32
  for +buf: List<&2, Char>
  for +isu: Bool
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.hiesc.hit.go(tl, hi, buf, stack, Pull.GNext{}, False{}, isu)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.hiesc(stack, Pull.GSkip{ee}, False{}, hi, isu)), ee)

def ls_he(tl, fn, hi, buf, isu, _stack, ee, gg, sel, _hsel, ih):
  match isu:
    case True{}:
      ih(Pull.MLo{3n, 0, hi, buf}, 2n+gg, {==})
    case False{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# the low half of a pair is in, both in step
law ls_le:
  for +tl: String
  for +fn: Nat
  for +lo: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +sur: Lex.Sur
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.lo.end.go(tl, lo, hi, buf, stack, Pull.GNext{}, False{}, sur)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.lo.end(tl, stack, Pull.GSkip{ee}, False{}, sur)), ee)

def ls_le(tl, fn, lo, hi, buf, sur, _stack, ee, gg, sel, _hsel, ih):
  match sur:
    case Lex.SLo{}:
      ih(Pull.MCopy{Char.from_u32(Lex.unicode.pair(hi, lo)) <> buf}, 2n+gg, {==})
    case Lex.SOk{}:
      kq_err(sel, fn, tl, 2n+gg, ee)
    case Lex.SHi{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# one more hex digit of a low half, both in step
law ls_lp:
  for +tl: String
  for +fn: Nat
  for +left2: Nat
  for +acc: U32
  for +hi: U32
  for +dig: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.lo.put(tl, left2, acc, hi, dig, buf, stack, Pull.GNext{}, False{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.lo.put(tl, left2, acc, hi, dig, stack, Pull.GSkip{ee}, False{})), ee)

def ls_lp(tl, fn, left2, acc, hi, dig, buf, stack, ee, gg, sel, hsel, ih):
  match left2:
    case 0n:
      ls_le(tl, fn, (acc * 16 + dig : U32), hi, buf, Lex.unicode.sur((acc * 16 + dig : U32)), stack, ee, gg, sel, hsel,
        ih)
    case 1n+pp:
      ih(Pull.MLo{pp, (acc * 16 + dig : U32), hi, buf}, 2n+gg, {==})

# one hex digit of a low half, both in step
law ls_lh:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +left2: Nat
  for +acc: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +ok: Bool
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  for ih: @m2: Pull.Mode -> @g2: Nat -> {isstr(m2) == True{} : Bool} -> kq(sel, Pull.next.go(1n+fn, tl, Pull.S{m2,
    stack, Pull.GNext{}, False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{skm(m2), stack, Pull.GSkip{ee},
    False{}, False{}}), ee)
  kq(sel, Pull.next.go(1n+fn, tl, Pull.lo.hit.go(ch, tl, left2, acc, hi, buf, stack, Pull.GNext{}, False{}, ok)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.sk.lo.go(ch, tl, left2, acc, hi, stack, Pull.GSkip{ee}, False{}, ok)), ee)

def ls_lh(tl, fn, ch, left2, acc, hi, buf, ok, stack, ee, gg, sel, hsel, ih):
  match ok:
    case True{}:
      ls_lp(tl, fn, left2, acc, hi, Lex.hex(ch), buf, stack, ee, gg, sel, hsel, ih)
    case False{}:
      kq_err(sel, fn, tl, 2n+gg, ee)

# a reader and a skip walk a string in step: both fail, or both close it on
# the same suffix
law ls_str:
  for +xx: String
  for +fn: Nat
  for +mn: Pull.Mode
  for +stack: List<&2, Pull.Frame>
  for +ee: Nat
  for +gg: Nat
  for +hs: {isstr(mn) == True{} : Bool}
  for +sel: Bool
  for +hsel: {selok(sel, stack) == True{} : Bool}
  kq(sel, Pull.next.go(1n+fn, xx, Pull.S{mn, stack, Pull.GNext{}, False{}, False{}}),
    Pull.next.go(1n+fu(xx, gg), xx, Pull.S{skm(mn), stack, Pull.GSkip{ee}, False{}, False{}}), ee)

def ls_str(xx, fn, mn, stack, ee, gg, hs, sel, hsel):
  match xx mn:
    case SNil{} Pull.MQuote{}:
      kq_bad(sel, ee)
    case SNil{} Pull.MSpan{+cut, +nn}:
      kq_bad(sel, ee)
    case SNil{} Pull.MCopy{+buf}:
      kq_bad(sel, ee)
    case SNil{} Pull.MEsc{+buf}:
      kq_bad(sel, ee)
    case SNil{} Pull.MUni{+left2, +acc, +buf}:
      kq_bad(sel, ee)
    case SNil{} Pull.MHi{+hi, +buf}:
      kq_bad(sel, ee)
    case SNil{} Pull.MHiEsc{+hi, +buf}:
      kq_bad(sel, ee)
    case SNil{} Pull.MLo{+left2, +acc, +hi, +buf}:
      kq_bad(sel, ee)
    case SCon{+ch, +tl} Pull.MQuote{}:
      ls_q(tl, fn, ch, Pull.span.kind.of(ch), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MSpan{+cut, +nn}:
      ls_sp(tl, fn, cut, nn, Pull.span.kind.of(ch), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MCopy{+buf}:
      ls_cp(tl, fn, ch, buf, Lex.classify(ch), U32.is_lt(Char.to_u32(ch), 32), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MEsc{+buf}:
      ls_es(tl, fn, ch, buf, U32.is_eq(Char.to_u32(ch), 117), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MUni{+left2, +acc, +buf}:
      ls_uh(tl, fn, ch, left2, acc, buf, Lex.hex.ok(Char.to_u32(ch)), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MHi{+hi, +buf}:
      ls_hi(tl, fn, hi, buf, Lex.classify(ch), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MHiEsc{+hi, +buf}:
      ls_he(tl, fn, hi, buf, U32.is_eq(Char.to_u32(ch), 117), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SCon{+ch, +tl} Pull.MLo{+left2, +acc, +hi, +buf}:
      ls_lh(tl, fn, ch, left2, acc, hi, buf, Lex.hex.ok(Char.to_u32(ch)), stack, ee, gg, sel, hsel,
        m2 => g2 => h2 => ls_str(tl, fn, m2, stack, ee, g2, h2, sel, hsel))
    case SNil{} Pull.MIdle{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MIdle{}), stack, Pull.GSkip{ee}, False{}, False{}}),
        ee), hs)
    case SCon{+b1, +b2} Pull.MIdle{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MIdle{}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SNil{} Pull.MWord{+a1, +a2, +a3}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MWord{a1, a2, a3}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MWord{a1, a2, a3}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MWord{+a1, +a2, +a3}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MWord{a1, a2, a3}, stack, Pull.GNext{}, False{},
        False{}}), Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MWord{a1, a2, a3}), stack,
        Pull.GSkip{ee}, False{}, False{}}), ee), hs)
    case SNil{} Pull.MSkStr{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkStr{}), stack, Pull.GSkip{ee}, False{}, False{}}),
        ee), hs)
    case SCon{+b1, +b2} Pull.MSkStr{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkStr{}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SNil{} Pull.MSkEsc{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkEsc{}), stack, Pull.GSkip{ee}, False{}, False{}}),
        ee), hs)
    case SCon{+b1, +b2} Pull.MSkEsc{}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkEsc{}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SNil{} Pull.MSkUni{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkUni{a1, a2}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkUni{a1, a2}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MSkUni{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkUni{a1, a2}, stack, Pull.GNext{}, False{},
          False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkUni{a1, a2}), stack, Pull.GSkip{ee},
        False{}, False{}}), ee), hs)
    case SNil{} Pull.MSkHi{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkHi{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkHi{a1}), stack, Pull.GSkip{ee}, False{}, False{}}),
        ee), hs)
    case SCon{+b1, +b2} Pull.MSkHi{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkHi{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkHi{a1}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SNil{} Pull.MSkHiEsc{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkHiEsc{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkHiEsc{a1}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MSkHiEsc{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkHiEsc{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkHiEsc{a1}), stack, Pull.GSkip{ee},
        False{}, False{}}), ee), hs)
    case SNil{} Pull.MSkLo{+a1, +a2, +a3}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MSkLo{a1, a2, a3}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MSkLo{a1, a2, a3}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MSkLo{+a1, +a2, +a3}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MSkLo{a1, a2, a3}, stack, Pull.GNext{}, False{},
        False{}}), Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MSkLo{a1, a2, a3}), stack,
        Pull.GSkip{ee}, False{}, False{}}), ee), hs)
    case SNil{} Pull.MDone{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MDone{a1, a2}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MDone{a1, a2}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MDone{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MDone{a1, a2}, stack, Pull.GNext{}, False{},
          False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MDone{a1, a2}), stack, Pull.GSkip{ee},
        False{}, False{}}), ee), hs)
    case SNil{} Pull.MRest{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MRest{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MRest{a1}), stack, Pull.GSkip{ee}, False{}, False{}}),
        ee), hs)
    case SCon{+b1, +b2} Pull.MRest{+a1}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MRest{a1}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MRest{a1}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SNil{} Pull.MJump{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SNil{}, Pull.S{Pull.MJump{a1, a2}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(SNil{}, gg), SNil{}, Pull.S{skm(Pull.MJump{a1, a2}), stack, Pull.GSkip{ee}, False{},
        False{}}), ee), hs)
    case SCon{+b1, +b2} Pull.MJump{+a1, +a2}:
      M1.no(kq(sel, Pull.next.go(1n+fn, SCon{b1, b2}, Pull.S{Pull.MJump{a1, a2}, stack, Pull.GNext{}, False{},
          False{}}),
        Pull.next.go(1n+fu(SCon{b1, b2}, gg), SCon{b1, b2}, Pull.S{skm(Pull.MJump{a1, a2}), stack, Pull.GSkip{ee},
        False{}, False{}}), ee), hs)

# laws/SkipPassesOneValue.bend: a reader and a skip in step between tokens, and through a word

# a reader's failed step claims nothing
law kr_err:
  for +fn: Nat
  for +tl: String
  for os: Pull.Out
  for +dd: Nat
  kr(Pull.next.go(1n+fn, tl, Pull.err.st(Pull.GNext{})), os, dd)

def kr_err(_fn, tl, _os, _dd):
  match tl:
    case SNil{}:
      Unit{}
    case SCon{_, _}:
      Unit{}

# a reader's finished step, on any budget and text
law krd:
  for +ff: Nat
  for +txt: String
  for +stop: Pull.Stop
  for +saved: String
  for +st: List<&2, Pull.Frame>
  for +dn: Bool
  for +bd: Bool
  for os: Pull.Out
  for +dd: Nat
  for hh: kr.g((stop, Pull.Cur{saved, st, dn, bd}), os, dd)
  kr(Pull.next.go(ff, txt, Pull.S{Pull.MDone{stop, saved}, st, Pull.GNext{}, dn, bd}), os, dd)

def krd(ff, txt, _stop, _saved, _st, _dn, _bd, _os, _dd, hh):
  match ff txt:
    case 0n SNil{}:
      hh
    case 0n SCon{_, _}:
      hh
    case 1n+_ SNil{}:
      hh
    case 1n+_ SCon{_, _}:
      hh

# a jump back from a word, or a step that already stopped
law jud:
  for +mm: Nat
  for +rest: String
  for +st: Pull.St
  {Pull.next.go(1n+1n+mm, "", Pull.jump.unless.done(rest, st)) == Pull.next.go(1n+mm, rest, st) : Pull.Out}

def jud(mm, rest, st):
  match st:
    case Pull.S{Pull.MDone{+stop, +saved}, +stack, +goal, +done, +bad}:
      Equal.sym(Pull.Out, Pull.next.go(1n+mm, rest, Pull.S{Pull.MDone{stop, saved}, stack, goal, done, bad}),
        Pull.Fin{(stop, Pull.Cur{saved, stack, done, bad})}, go_md(1n+mm, rest, stop, saved, stack, goal, done, bad))
    case Pull.S{Pull.MIdle{}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MWord{+a1, +a2, +a3}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSpan{+a1, +a2}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MCopy{+a1}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MEsc{+a1}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MUni{+a1, +a2, +a3}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MHi{+a1, +a2}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MHiEsc{+a1, +a2}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MLo{+a1, +a2, +a3, +a4}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkStr{}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkUni{+a1, +a2}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkHi{+a1}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkHiEsc{+a1}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MSkLo{+a1, +a2, +a3}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MRest{+a1}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MQuote{}, +stack, +goal, +done, +bad}:
      {==}
    case Pull.S{Pull.MJump{+a1, +a2}, +stack, +goal, +done, +bad}:
      {==}

# the delimiter after a word inside a skipped array: taken, or read between tokens
law lp_arr:
  for +outer: List<&2, Pull.Frame>
  for +kk: Nat
  for +ch: Char
  for +cls: Lex.Class
  {Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, cls)
    == Pull.look.plan(ch, Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, False{}, cls) : Pull.St}

def lp_arr(_outer, _kk, _ch, cls):
  match cls:
    case Lex.CSpace{}:
      {==}
    case Lex.CPunct{_}:
      {==}
    case Lex.CQuote{}:
      {==}
    case Lex.CBack{}:
      {==}
    case Lex.COther{}:
      {==}

# the delimiter after a word inside a skipped object: taken, or read between tokens
law lp_obj:
  for +outer: List<&2, Pull.Frame>
  for +kk: Nat
  for +ch: Char
  for +cls: Lex.Class
  {Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, cls)
    == Pull.look.plan(ch, Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, False{}, cls) : Pull.St}

def lp_obj(_outer, _kk, _ch, cls):
  match cls:
    case Lex.CSpace{}:
      {==}
    case Lex.CPunct{_}:
      {==}
    case Lex.CQuote{}:
      {==}
    case Lex.CBack{}:
      {==}
    case Lex.COther{}:
      {==}

# where a word run leaves the text: the delimiter and what follows it
def wvirt(got: (String & Pull.Wst)) -> String:
  match got:
    case (rest, Pull.WStop{_, _, _, ch}):
      SCon{ch, rest}
    case (_, Pull.WEof{_, _, _}):
      ""
    case (rest, Pull.WMore{_, _, _}):
      rest

# two more jumps of budget for a character kept in a word
def wstep(st: Pull.Wst, acc: Nat) -> Nat:
  match st:
    case Pull.WMore{_, _, _}:
      2n+acc
    case _:
      acc

# the budget a word run adds: two for each character it keeps
def wacc(txt: String, st: Pull.Wst, acc: Nat) -> Nat:
  match txt st:
    case SCon{+c, tl} Pull.WMore{buf, nn, num}:
      +de = Pull.word.decide(c, Char.to_u32(c), buf, nn, num)
      wacc(tl, de, wstep(de, acc))
    case _ _:
      acc

# one character of a word run, once it is known to be kept or not
law wr_k:
  for +c: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  for +keep: Bool
  for ih: @b2: List<&2, Char> -> @n2: U32 -> @m2: V.Num -> @a2: Nat -> {fu(tl, a2)
    == fu(wvirt(Pull.word.run(tl, Pull.WMore{b2, n2, m2})), wacc(tl, Pull.WMore{b2, n2, m2}, a2)) : Nat}
  {fu(tl, 2n+acc) == fu(wvirt(Pull.word.run(tl, Pull.word.keep.go(c, Char.to_u32(c), buf, nn, num, keep))),
    wacc(tl, Pull.word.keep.go(c, Char.to_u32(c), buf, nn, num, keep), wstep(Pull.word.keep.go(c, Char.to_u32(c), buf,
    nn, num, keep), acc))) : Nat}

def wr_k(c, tl, buf, nn, num, acc, keep, ih):
  match tl keep:
    case SNil{} True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case SCon{_, _} True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case SNil{} False{}:
      {==}
    case SCon{_, _} False{}:
      {==}

# one character of a word run
law wr_c:
  for +c: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  for +dig: Bool
  for ih: @b2: List<&2, Char> -> @n2: U32 -> @m2: V.Num -> @a2: Nat -> {fu(tl, a2)
    == fu(wvirt(Pull.word.run(tl, Pull.WMore{b2, n2, m2})), wacc(tl, Pull.WMore{b2, n2, m2}, a2)) : Nat}
  {fu(tl, 2n+acc) == fu(wvirt(Pull.word.run(tl, Pull.word.digit.go(c, Char.to_u32(c), buf, nn, num, dig))),
    wacc(tl, Pull.word.digit.go(c, Char.to_u32(c), buf, nn, num, dig), wstep(Pull.word.digit.go(c, Char.to_u32(c), buf,
    nn, num, dig), acc))) : Nat}

def wr_c(c, tl, buf, nn, num, acc, dig, ih):
  match dig:
    case True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case False{}:
      wr_k(c, tl, buf, nn, num, acc, Bool.not(Pull.word.special(Char.to_u32(c))), ih)

# the budget over a word's text is the budget from its delimiter on, and two
# for each character the run kept
law wr_fu:
  for +txt: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  {fu(txt, acc) == fu(wvirt(Pull.word.run(txt, Pull.WMore{buf, nn, num})), wacc(txt, Pull.WMore{buf, nn, num}, acc))
    : Nat}

def wr_fu(txt, buf, nn, num, acc):
  match txt:
    case SNil{}:
      {==}
    case SCon{+c, +tl}:
      wr_c(c, tl, buf, nn, num, acc, V.num.ok.digit(Char.to_u32(c)), b2 => n2 => m2 => a2 => wr_fu(tl, b2, n2, m2, a2))

# one character of a word run, kept or not: two more on top is two more
law was_k:
  for +c: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  for +keep: Bool
  for ih: @b2: List<&2, Char> -> @n2: U32 -> @m2: V.Num -> @a2: Nat -> {wacc(tl, Pull.WMore{b2, n2, m2}, 2n+a2)
    == 2n+wacc(tl, Pull.WMore{b2, n2, m2}, a2) : Nat}
  {wacc(tl, Pull.word.keep.go(c, Char.to_u32(c), buf, nn, num, keep), wstep(Pull.word.keep.go(c, Char.to_u32(c), buf,
    nn, num, keep), 2n+acc)) == 2n+wacc(tl, Pull.word.keep.go(c, Char.to_u32(c), buf, nn, num, keep),
    wstep(Pull.word.keep.go(c, Char.to_u32(c), buf, nn, num, keep), acc)) : Nat}

def was_k(c, tl, buf, nn, num, acc, keep, ih):
  match tl keep:
    case SNil{} True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case SCon{_, _} True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case SNil{} False{}:
      {==}
    case SCon{_, _} False{}:
      {==}

# one character of a word run: two more on top is two more
law was_c:
  for +c: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  for +dig: Bool
  for ih: @b2: List<&2, Char> -> @n2: U32 -> @m2: V.Num -> @a2: Nat -> {wacc(tl, Pull.WMore{b2, n2, m2}, 2n+a2)
    == 2n+wacc(tl, Pull.WMore{b2, n2, m2}, a2) : Nat}
  {wacc(tl, Pull.word.digit.go(c, Char.to_u32(c), buf, nn, num, dig), wstep(Pull.word.digit.go(c, Char.to_u32(c), buf,
    nn, num, dig), 2n+acc)) == 2n+wacc(tl, Pull.word.digit.go(c, Char.to_u32(c), buf, nn, num, dig),
    wstep(Pull.word.digit.go(c, Char.to_u32(c), buf, nn, num, dig), acc)) : Nat}

def was_c(c, tl, buf, nn, num, acc, dig, ih):
  match dig:
    case True{}:
      ih(c <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(c)), 2n+acc)
    case False{}:
      was_k(c, tl, buf, nn, num, acc, Bool.not(Pull.word.special(Char.to_u32(c))), ih)

# two more on top of a word run's budget is two more
law wacc_s:
  for +txt: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +acc: Nat
  {wacc(txt, Pull.WMore{buf, nn, num}, 2n+acc) == 2n+wacc(txt, Pull.WMore{buf, nn, num}, acc) : Nat}

def wacc_s(txt, buf, nn, num, acc):
  match txt:
    case SNil{}:
      {==}
    case SCon{+c, +tl}:
      was_c(c, tl, buf, nn, num, acc, V.num.ok.digit(Char.to_u32(c)), b2 => n2 => m2 => a2 => wacc_s(tl, b2, n2, m2,
        a2))

# laws/SkipPassesOneValue.bend: a reader and a skip in step at the end of a word

# a null that ends the text, on a skip at depth 0
law we0_null:
  for +fn: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENull{}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.place.val.on(Pull.ENull{}, "", Pull.GSkip{0n}, spot)), 0n)

def we0_null(fn, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.ENull{}, "", Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, "", st, root, False{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.ENull{}, "", Pull.GSkip{0n}, Pull.Spot{st, root})), 0n, {==})

# a null that ends the text, on a skip inside a container
law we1_null:
  for +fn: Nat
  for +kk: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENull{}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

def we1_null(fn, kk, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, True{}}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, "", st, True{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, False{}}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, "", st, False{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, (0n, {==}))

# a true that ends the text, on a skip at depth 0
law we0_true:
  for +fn: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{True{}}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.place.val.on(Pull.EBool{True{}}, "", Pull.GSkip{0n}, spot)), 0n)

def we0_true(fn, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.EBool{True{}}, "", Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, "", st, root, False{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.EBool{True{}}, "", Pull.GSkip{0n}, Pull.Spot{st, root})), 0n, {==})

# a true that ends the text, on a skip inside a container
law we1_true:
  for +fn: Nat
  for +kk: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{True{}}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

def we1_true(fn, kk, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, True{}}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, "", st, True{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, False{}}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, "", st, False{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, (0n, {==}))

# a false that ends the text, on a skip at depth 0
law we0_false:
  for +fn: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{False{}}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.place.val.on(Pull.EBool{False{}}, "", Pull.GSkip{0n}, spot)), 0n)

def we0_false(fn, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.EBool{False{}}, "", Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, "", st, root, False{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.EBool{False{}}, "", Pull.GSkip{0n}, Pull.Spot{st, root})), 0n, {==})

# a false that ends the text, on a skip inside a container
law we1_false:
  for +fn: Nat
  for +kk: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{False{}}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

def we1_false(fn, kk, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, True{}}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, "", st, True{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, False{}}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, "", st, False{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, (0n, {==}))

# a num that ends the text, on a skip at depth 0
law we0_num:
  for +fn: Nat
  for +raw: String
  for +nn: U32
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENum{raw, nn}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.place.val.on(Pull.ENum{raw, nn}, "", Pull.GSkip{0n}, spot)), 0n)

def we0_num(fn, raw, nn, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.ENum{raw, nn}, "", Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, "", st, root, False{}, Pull.next.go(2n+aw, "",
        Pull.place.val.on(Pull.ENum{raw, nn}, "", Pull.GSkip{0n}, Pull.Spot{st, root})), 0n, {==})

# a num that ends the text, on a skip inside a container
law we1_num:
  for +fn: Nat
  for +raw: String
  for +nn: U32
  for +kk: Nat
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENum{raw, nn}, "", Pull.GNext{}, spot)), Pull.next.go(2n+aw, "",
    Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

def we1_num(fn, raw, nn, kk, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, True{}}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, "", st, True{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.Spot{+st, False{}}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, "", st, False{}, False{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, (0n, {==}))

# a word that ends the text
law we0:
  for +fn: Nat
  for +raw: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +aw: Nat
  for +atom: Pull.Atom
  kr(Pull.next.go(fn, "", Pull.word.eof.place(atom, raw, nn, stack, Pull.GNext{})), Pull.next.go(2n+aw, "",
    Pull.word.eof.place(atom, raw, nn, stack, Pull.GSkip{0n})), 0n)

def we0(fn, raw, nn, stack, aw, atom):
  match atom:
    case Pull.ABad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.word.eof.place(Pull.ABad{}, raw, nn, stack, Pull.GSkip{0n})), 0n, Unit{})
    case Pull.ANull{}:
      we0_null(fn, aw, Pull.place.spot(stack))
    case Pull.ATrue{}:
      we0_true(fn, aw, Pull.place.spot(stack))
    case Pull.AFalse{}:
      we0_false(fn, aw, Pull.place.spot(stack))
    case Pull.ANum{}:
      we0_num(fn, raw, nn, aw, Pull.place.spot(stack))

# a word that ends the text
law we1:
  for +fn: Nat
  for +raw: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  for +atom: Pull.Atom
  kr(Pull.next.go(fn, "", Pull.word.eof.place(atom, raw, nn, stack, Pull.GNext{})), Pull.next.go(2n+aw, "",
    Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

def we1(fn, raw, nn, stack, kk, aw, atom):
  match atom:
    case Pull.ABad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(2n+aw, "",
        Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Pull.ANull{}:
      we1_null(fn, kk, aw, Pull.place.spot(stack))
    case Pull.ATrue{}:
      we1_true(fn, kk, aw, Pull.place.spot(stack))
    case Pull.AFalse{}:
      we1_false(fn, kk, aw, Pull.place.spot(stack))
    case Pull.ANum{}:
      we1_num(fn, raw, nn, kk, aw, Pull.place.spot(stack))

# a word that ends the text, for both
law weof:
  for +fn: Nat
  for +raw: String
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.eof.place(Pull.word.kind(raw, nn, num), raw, nn, stack, Pull.GNext{})),
    Pull.next.go(2n+aw, "", Pull.word.burst.eof.raw(raw, nn, num, stack, Pull.GSkip{dd})), dd)

def weof(fn, raw, nn, num, stack, dd, aw):
  match dd:
    case 0n:
      we0(fn, raw, nn, stack, aw, Pull.word.kind(raw, nn, num))
    case 1n+kk:
      we1(fn, raw, nn, stack, kk, aw, Pull.word.kind(raw, nn, num))

# a skip resumes after a word where a reader would, on the budget the word left
law wsk_arr:
  for +rest: String
  for +ch: Char
  for +outer: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  {Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.jump.unless.done(rest, Pull.lay.plan(Pull.FArr{Pull.SCom{},
    False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch))))
    == Pull.next.go(1n+fu(SCon{ch, rest}, aw), SCon{ch, rest}, Pull.S{Pull.MIdle{}, Pull.FArr{Pull.SCom{},
      False{}} <> outer, Pull.GSkip{1n+kk}, False{}, False{}}) : Pull.Out}

def wsk_arr(rest, ch, outer, kk, aw):
  ef = Equal.trans(Nat, fu(rest, 1n+1n+2n+aw), 1n+fu(rest, 1n+2n+aw), 1n+1n+fu(rest, 2n+aw),
    fu_s(rest, 1n+2n+aw), Equal.cong(Nat, Nat, zz => 1n+zz, fu(rest, 1n+2n+aw), 1n+fu(rest, 2n+aw), fu_s(rest, 2n+aw)))
  eg = Equal.cong(Nat, Pull.Out, zz => Pull.next.go(zz, "", Pull.jump.unless.done(rest,
    Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))), fu(rest,
    1n+1n+2n+aw),
    1n+1n+fu(rest, 2n+aw), ef)
  ej = jud(fu(rest, 2n+aw), rest, Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk},
    Lex.classify(ch)))
  el = Equal.cong(Pull.St, Pull.Out, zz => Pull.next.go(1n+fu(rest, 2n+aw), rest, zz),
    Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)),
    Pull.look.plan(ch, Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, False{}, Lex.classify(ch)),
      lp_arr(outer, kk, ch, Lex.classify(ch)))
  Equal.trans(Pull.Out, Pull.next.go(fu(rest, 1n+1n+2n+aw), "", Pull.jump.unless.done(rest,
    Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
    Pull.next.go(1n+1n+fu(rest, 2n+aw), "", Pull.jump.unless.done(rest, Pull.lay.plan(Pull.FArr{Pull.SCom{},
    False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
    Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.look.plan(ch, Pull.FArr{Pull.SCom{}, False{}} <> outer,
      Pull.GSkip{1n+kk}, False{}, Lex.classify(ch))), eg,
    Equal.trans(Pull.Out, Pull.next.go(1n+1n+fu(rest, 2n+aw), "", Pull.jump.unless.done(rest,
      Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
      Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.lay.plan(Pull.FArr{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk},
        Lex.classify(ch))),
      Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.look.plan(ch, Pull.FArr{Pull.SCom{}, False{}} <> outer,
        Pull.GSkip{1n+kk}, False{}, Lex.classify(ch))),
      ej, el))

# a skip resumes after a word where a reader would, on the budget the word left
law wsk_obj:
  for +rest: String
  for +ch: Char
  for +outer: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  {Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.jump.unless.done(rest, Pull.lay.plan(Pull.FObj{Pull.SCom{},
    False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch))))
    == Pull.next.go(1n+fu(SCon{ch, rest}, aw), SCon{ch, rest}, Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SCom{},
      False{}} <> outer, Pull.GSkip{1n+kk}, False{}, False{}}) : Pull.Out}

def wsk_obj(rest, ch, outer, kk, aw):
  ef = Equal.trans(Nat, fu(rest, 1n+1n+2n+aw), 1n+fu(rest, 1n+2n+aw), 1n+1n+fu(rest, 2n+aw),
    fu_s(rest, 1n+2n+aw), Equal.cong(Nat, Nat, zz => 1n+zz, fu(rest, 1n+2n+aw), 1n+fu(rest, 2n+aw), fu_s(rest, 2n+aw)))
  eg = Equal.cong(Nat, Pull.Out, zz => Pull.next.go(zz, "", Pull.jump.unless.done(rest,
    Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))), fu(rest,
    1n+1n+2n+aw),
    1n+1n+fu(rest, 2n+aw), ef)
  ej = jud(fu(rest, 2n+aw), rest, Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk},
    Lex.classify(ch)))
  el = Equal.cong(Pull.St, Pull.Out, zz => Pull.next.go(1n+fu(rest, 2n+aw), rest, zz),
    Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)),
    Pull.look.plan(ch, Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, False{}, Lex.classify(ch)),
      lp_obj(outer, kk, ch, Lex.classify(ch)))
  Equal.trans(Pull.Out, Pull.next.go(fu(rest, 1n+1n+2n+aw), "", Pull.jump.unless.done(rest,
    Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
    Pull.next.go(1n+1n+fu(rest, 2n+aw), "", Pull.jump.unless.done(rest, Pull.lay.plan(Pull.FObj{Pull.SCom{},
    False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
    Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.look.plan(ch, Pull.FObj{Pull.SCom{}, False{}} <> outer,
      Pull.GSkip{1n+kk}, False{}, Lex.classify(ch))), eg,
    Equal.trans(Pull.Out, Pull.next.go(1n+1n+fu(rest, 2n+aw), "", Pull.jump.unless.done(rest,
      Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk}, Lex.classify(ch)))),
      Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.lay.plan(Pull.FObj{Pull.SCom{}, False{}} <> outer, Pull.GSkip{1n+kk},
        Lex.classify(ch))),
      Pull.next.go(1n+fu(rest, 2n+aw), rest, Pull.look.plan(ch, Pull.FObj{Pull.SCom{}, False{}} <> outer,
        Pull.GSkip{1n+kk}, False{}, Lex.classify(ch))),
      ej, el))

# a null ended by a delimiter, on a skip at depth 0
law ws0_null:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENull{}, SCon{ch, rest}, Pull.GNext{}, spot)),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.place.val.on(Pull.ENull{}, SCon{ch, rest}, Pull.GSkip{0n}, spot)),
    0n)

def ws0_null(fn, rest, ch, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.place.val.on(Pull.ENull{}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, SCon{ch, rest}, st, root, False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw),
        "", Pull.place.val.on(Pull.ENull{}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.Spot{st, root})), 0n,
        go_md(fu(SCon{ch, rest}, 2n+aw), "", Pull.SSkip{}, SCon{ch, rest}, st, Pull.GSkip{0n}, root, False{}))

# a null ended by a delimiter, on a skip inside a container
law ws1_null:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.ENull{}, ch, rest, stack, Pull.GNext{})), Pull.next.go(fu(SCon{ch,
    rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENull{}, ch, rest, stack, Pull.GSkip{1n+kk})), 1n+kk)

def ws1_null(fn, rest, ch, stack, kk, aw):
  match stack:
    case Nil{}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, SCon{ch, rest}, [], True{}, False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw),
        "", Pull.word.burst.goal(Pull.ENull{}, ch, rest, Nil{}, Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, SCon{ch, rest}, Pull.FArr{Pull.SCom{}, False{}} <> outer, False{}, False{},
        Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENull{}, ch, rest,
        Con{Pull.FArr{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_arr(rest, ch, outer, kk, aw)))
    case Con{Pull.FArr{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FArr{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})
    case Con{Pull.FArr{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FArr{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})
    case Con{Pull.FArr{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FArr{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})
    case Con{Pull.FObj{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.ENull{}}, SCon{ch, rest}, Pull.FObj{Pull.SCom{}, False{}} <> outer, False{}, False{},
        Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENull{}, ch, rest,
        Con{Pull.FObj{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_obj(rest, ch, outer, kk, aw)))
    case Con{Pull.FObj{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FObj{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})
    case Con{Pull.FObj{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FObj{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})
    case Con{Pull.FObj{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENull{}, ch, rest, Con{Pull.FObj{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})), 1n+kk,
        Unit{})

# a null ended by a delimiter, for both
law ws_null:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.ENull{}, ch, rest, stack, Pull.GNext{})), Pull.next.go(fu(SCon{ch,
    rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENull{}, ch, rest, stack, Pull.GSkip{dd})), dd)

def ws_null(fn, rest, ch, stack, dd, aw):
  match dd:
    case 0n:
      ws0_null(fn, rest, ch, aw, Pull.place.spot(stack))
    case 1n+kk:
      ws1_null(fn, rest, ch, stack, kk, aw)

# a true ended by a delimiter, on a skip at depth 0
law ws0_true:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{True{}}, SCon{ch, rest}, Pull.GNext{}, spot)),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.place.val.on(Pull.EBool{True{}}, SCon{ch, rest}, Pull.GSkip{0n},
    spot)), 0n)

def ws0_true(fn, rest, ch, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.place.val.on(Pull.EBool{True{}}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, SCon{ch, rest}, st, root, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.place.val.on(Pull.EBool{True{}}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.Spot{st, root})), 0n,
        go_md(fu(SCon{ch, rest}, 2n+aw), "", Pull.SSkip{}, SCon{ch, rest}, st, Pull.GSkip{0n}, root, False{}))

# a true ended by a delimiter, on a skip inside a container
law ws1_true:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, stack,
    Pull.GSkip{1n+kk})), 1n+kk)

def ws1_true(fn, rest, ch, stack, kk, aw):
  match stack:
    case Nil{}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, SCon{ch, rest}, [], True{}, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Nil{}, Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, SCon{ch, rest}, Pull.FArr{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest,
        Con{Pull.FArr{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_arr(rest, ch, outer, kk, aw)))
    case Con{Pull.FArr{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FArr{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FArr{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FArr{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EBool{True{}}}, SCon{ch, rest}, Pull.FObj{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest,
        Con{Pull.FObj{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_obj(rest, ch, outer, kk, aw)))
    case Con{Pull.FObj{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FObj{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FObj{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, Con{Pull.FObj{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})

# a true ended by a delimiter, for both
law ws_true:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{True{}}, ch, rest, stack,
    Pull.GSkip{dd})), dd)

def ws_true(fn, rest, ch, stack, dd, aw):
  match dd:
    case 0n:
      ws0_true(fn, rest, ch, aw, Pull.place.spot(stack))
    case 1n+kk:
      ws1_true(fn, rest, ch, stack, kk, aw)

# a false ended by a delimiter, on a skip at depth 0
law ws0_false:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.EBool{False{}}, SCon{ch, rest}, Pull.GNext{}, spot)),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.place.val.on(Pull.EBool{False{}}, SCon{ch, rest}, Pull.GSkip{0n},
    spot)), 0n)

def ws0_false(fn, rest, ch, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.place.val.on(Pull.EBool{False{}}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, SCon{ch, rest}, st, root, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.place.val.on(Pull.EBool{False{}}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.Spot{st, root})), 0n,
        go_md(fu(SCon{ch, rest}, 2n+aw), "", Pull.SSkip{}, SCon{ch, rest}, st, Pull.GSkip{0n}, root, False{}))

# a false ended by a delimiter, on a skip inside a container
law ws1_false:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, stack,
    Pull.GSkip{1n+kk})), 1n+kk)

def ws1_false(fn, rest, ch, stack, kk, aw):
  match stack:
    case Nil{}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, SCon{ch, rest}, [], True{}, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Nil{}, Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, SCon{ch, rest}, Pull.FArr{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest,
        Con{Pull.FArr{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_arr(rest, ch, outer, kk, aw)))
    case Con{Pull.FArr{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FArr{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FArr{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FArr{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EBool{False{}}}, SCon{ch, rest}, Pull.FObj{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest,
        Con{Pull.FObj{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_obj(rest, ch, outer, kk, aw)))
    case Con{Pull.FObj{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FObj{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FObj{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, Con{Pull.FObj{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})

# a false ended by a delimiter, for both
law ws_false:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.EBool{False{}}, ch, rest, stack,
    Pull.GSkip{dd})), dd)

def ws_false(fn, rest, ch, stack, dd, aw):
  match dd:
    case 0n:
      ws0_false(fn, rest, ch, aw, Pull.place.spot(stack))
    case 1n+kk:
      ws1_false(fn, rest, ch, stack, kk, aw)

# a num ended by a delimiter, on a skip at depth 0
law ws0_num:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +raw: String
  for +nn: U32
  for +aw: Nat
  for +spot: Pull.Spot
  kr(Pull.next.go(fn, "", Pull.place.val.on(Pull.ENum{raw, nn}, SCon{ch, rest}, Pull.GNext{}, spot)),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.place.val.on(Pull.ENum{raw, nn}, SCon{ch, rest}, Pull.GSkip{0n},
    spot)), 0n)

def ws0_num(fn, rest, ch, raw, nn, aw, spot):
  match spot:
    case Pull.SpotBad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.place.val.on(Pull.ENum{raw, nn}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.SpotBad{})), 0n, Unit{})
    case Pull.Spot{+st, +root}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, SCon{ch, rest}, st, root, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.place.val.on(Pull.ENum{raw, nn}, SCon{ch, rest}, Pull.GSkip{0n}, Pull.Spot{st, root})), 0n,
        go_md(fu(SCon{ch, rest}, 2n+aw), "", Pull.SSkip{}, SCon{ch, rest}, st, Pull.GSkip{0n}, root, False{}))

# a num ended by a delimiter, on a skip inside a container
law ws1_num:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +raw: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +kk: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, stack,
    Pull.GSkip{1n+kk})), 1n+kk)

def ws1_num(fn, rest, ch, raw, nn, stack, kk, aw):
  match stack:
    case Nil{}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, SCon{ch, rest}, [], True{}, False{}, Pull.next.go(fu(SCon{ch, rest},
        2n+aw), "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Nil{}, Pull.GSkip{1n+kk})), 1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, SCon{ch, rest}, Pull.FArr{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest,
        Con{Pull.FArr{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_arr(rest, ch, outer, kk, aw)))
    case Con{Pull.FArr{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FArr{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FArr{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FArr{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FArr{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SVal{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.ENum{raw, nn}}, SCon{ch, rest}, Pull.FObj{Pull.SCom{}, False{}} <> outer, False{},
        False{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest,
        Con{Pull.FObj{Pull.SVal{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, (aw, wsk_obj(rest, ch, outer, kk, aw)))
    case Con{Pull.FObj{Pull.SCom{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FObj{Pull.SCom{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SKey{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FObj{Pull.SKey{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})
    case Con{Pull.FObj{Pull.SCol{}, +f}, +outer}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, Con{Pull.FObj{Pull.SCol{}, f}, outer}, Pull.GSkip{1n+kk})),
        1n+kk, Unit{})

# a num ended by a delimiter, for both
law ws_num:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +raw: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, stack, Pull.GNext{})),
    Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "", Pull.word.burst.goal(Pull.ENum{raw, nn}, ch, rest, stack,
    Pull.GSkip{dd})), dd)

def ws_num(fn, rest, ch, raw, nn, stack, dd, aw):
  match dd:
    case 0n:
      ws0_num(fn, rest, ch, raw, nn, aw, Pull.place.spot(stack))
    case 1n+kk:
      ws1_num(fn, rest, ch, raw, nn, stack, kk, aw)

# a word ended by a delimiter, for both
law wstop:
  for +fn: Nat
  for +rest: String
  for +ch: Char
  for +raw: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  for +atom: Pull.Atom
  kr(Pull.next.go(fn, "", Pull.word.burst.atom(rest, ch, raw, nn, stack, Pull.GNext{}, atom)), Pull.next.go(fu(SCon{ch,
    rest}, 2n+aw), "", Pull.word.burst.atom(rest, ch, raw, nn, stack, Pull.GSkip{dd}, atom)), dd)

def wstop(fn, rest, ch, raw, nn, stack, dd, aw, atom):
  match atom:
    case Pull.ABad{}:
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(SCon{ch, rest}, 2n+aw), "",
        Pull.word.burst.atom(rest, ch, raw, nn, stack, Pull.GSkip{dd}, Pull.ABad{})), dd, Unit{})
    case Pull.ANull{}:
      ws_null(fn, rest, ch, stack, dd, aw)
    case Pull.ATrue{}:
      ws_true(fn, rest, ch, stack, dd, aw)
    case Pull.AFalse{}:
      ws_false(fn, rest, ch, stack, dd, aw)
    case Pull.ANum{}:
      ws_num(fn, rest, ch, raw, nn, stack, dd, aw)

# the end of a word run, for both
law ls_wat:
  for got: (String & Pull.Wst)
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +aw: Nat
  kr(Pull.next.go(fn, "", Pull.word.burst.at(got, stack, Pull.GNext{})), Pull.next.go(fu(wvirt(got), 2n+aw), "",
    Pull.word.burst.at(got, stack, Pull.GSkip{dd})), dd)

def ls_wat(got, fn, stack, dd, aw):
  match got:
    case (+rest, Pull.WEof{+b, +n, +m}):
      weof(fn, Lex.text(b), n, m, stack, dd, aw)
    case (+rest, Pull.WStop{+b, +n, +m, +ch}):
      wstop(fn, rest, ch, Lex.text(b), n, stack, dd, aw, Pull.word.kind(Lex.text(b), n, m))
    case (+rest, Pull.WMore{+b, +n, +m}):
      krd(fn, "", Pull.SEv{Pull.EErr{}}, "", [], False{}, True{}, Pull.next.go(fu(rest, 2n+aw), "",
        Pull.word.burst.at((rest, Pull.WMore{b, n, m}), stack,
        Pull.GSkip{dd})), dd, Unit{})

# a word, for both
law ls_mword:
  for +yy: String
  for +fn: Nat
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +g0: Nat
  kr(Pull.next.go(1n+fn, yy, Pull.S{Pull.MWord{buf, nn, num}, stack, Pull.GNext{}, False{}, False{}}),
    Pull.next.go(1n+fu(yy, 2n+g0), yy, Pull.S{Pull.MWord{buf, nn, num}, stack, Pull.GSkip{dd}, False{}, False{}}), dd)

def ls_mword(yy, fn, buf, nn, num, stack, dd, g0):
  match yy:
    case SNil{}:
      e = Equal.sym(Nat, fu(SNil{}, 2n+g0), fu(wvirt(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num})), 2n+wacc(SNil{},
        Pull.WMore{buf, nn, num}, g0)),
        Equal.trans(Nat, fu(SNil{}, 2n+g0), fu(wvirt(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num})), wacc(SNil{},
          Pull.WMore{buf, nn, num}, 2n+g0)), fu(wvirt(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num})), 2n+wacc(SNil{},
          Pull.WMore{buf, nn, num}, g0)),
          wr_fu(SNil{}, buf, nn, num, 2n+g0), Equal.cong(Nat, Nat, zz => fu(wvirt(Pull.word.run(SNil{}, Pull.WMore{buf,
            nn, num})), zz), wacc(SNil{}, Pull.WMore{buf, nn, num}, 2n+g0),
            2n+wacc(SNil{}, Pull.WMore{buf, nn, num}, g0), wacc_s(SNil{}, buf, nn, num, g0))))
      %e : kr(Pull.next.go(fn, "", Pull.word.burst.at(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num}), stack,
        Pull.GNext{})), Pull.next.go(_, "",
        Pull.word.burst.at(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num}), stack, Pull.GSkip{dd})), dd)
      ls_wat(Pull.word.run(SNil{}, Pull.WMore{buf, nn, num}), fn, stack, dd, wacc(SNil{}, Pull.WMore{buf, nn, num}, g0))
    case SCon{+c, +t}:
      e = Equal.sym(Nat, fu(SCon{c, t}, 2n+g0), fu(wvirt(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn, num})),
        2n+wacc(SCon{c, t}, Pull.WMore{buf, nn, num}, g0)),
        Equal.trans(Nat, fu(SCon{c, t}, 2n+g0), fu(wvirt(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn, num})),
          wacc(SCon{c, t}, Pull.WMore{buf, nn, num}, 2n+g0)), fu(wvirt(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn,
          num})), 2n+wacc(SCon{c, t}, Pull.WMore{buf, nn, num}, g0)),
          wr_fu(SCon{c, t}, buf, nn, num, 2n+g0), Equal.cong(Nat, Nat, zz => fu(wvirt(Pull.word.run(SCon{c, t},
            Pull.WMore{buf, nn, num})), zz), wacc(SCon{c, t}, Pull.WMore{buf, nn, num}, 2n+g0),
            2n+wacc(SCon{c, t}, Pull.WMore{buf, nn, num}, g0), wacc_s(SCon{c, t}, buf, nn, num, g0))))
      %e : kr(Pull.next.go(fn, "", Pull.word.burst.at(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn, num}), stack,
        Pull.GNext{})), Pull.next.go(_, "",
        Pull.word.burst.at(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn, num}), stack, Pull.GSkip{dd})), dd)
      ls_wat(Pull.word.run(SCon{c, t}, Pull.WMore{buf, nn, num}), fn, stack, dd, wacc(SCon{c, t}, Pull.WMore{buf, nn,
        num}, g0))

# a word's first character, for both
law ls_word0:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for +ok: Bool
  kr(Pull.next.go(1n+fn, tl, Pull.look.word(ch, stack, Pull.GNext{}, False{}, ok)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.look.word(ch, stack, Pull.GSkip{dd}, False{}, ok)), dd)

def ls_word0(tl, fn, ch, stack, dd, gg, ok):
  match ok:
    case True{}:
      ls_mword(tl, fn, ch <> [], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch)), stack, dd, gg)
    case False{}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)

# laws/SkipPassesOneValue.bend: a reader and a skip in step between tokens

# a `[`, for both
law lo_arr:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for +ok: Bool
  kr(Pull.next.go(1n+fn, tl, Pull.punct.arr.if(stack, Pull.GNext{}, ok)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.punct.arr.if(stack, Pull.GSkip{dd}, ok)), dd)

def lo_arr(tl, _fn, _stack, _dd, gg, ok):
  match tl ok:
    case SNil{} True{}:
      (2n+gg, {==})
    case SNil{} False{}:
      Unit{}
    case SCon{+c1, +t1} True{}:
      (2n+gg, {==})
    case SCon{+c1, +t1} False{}:
      Unit{}

# a `{`, for both
law lo_obj:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for +ok: Bool
  kr(Pull.next.go(1n+fn, tl, Pull.punct.obj.if(stack, Pull.GNext{}, ok)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.punct.obj.if(stack, Pull.GSkip{dd}, ok)), dd)

def lo_obj(tl, _fn, _stack, _dd, gg, ok):
  match tl ok:
    case SNil{} True{}:
      (2n+gg, {==})
    case SNil{} False{}:
      Unit{}
    case SCon{+c1, +t1} True{}:
      (2n+gg, {==})
    case SCon{+c1, +t1} False{}:
      Unit{}

# a `]`, for both
law lc_arr:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  kr(Pull.next.go(1n+fn, tl, Pull.close.arr(stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.close.arr(stack, Pull.GSkip{dd})), dd)

def lc_arr(tl, _fn, stack, dd, gg):
  match tl stack dd:
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Nil{}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Nil{}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Nil{} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Nil{} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Nil{}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Nil{}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Nil{} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Nil{} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}

# a `}`, for both
law lc_obj:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  kr(Pull.next.go(1n+fn, tl, Pull.close.obj(stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.close.obj(stack, Pull.GSkip{dd})), dd)

def lc_obj(tl, _fn, stack, dd, gg):
  match tl stack dd:
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Nil{}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Nil{}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SNil{} Nil{} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SNil{} Nil{} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCom{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SNil{} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Nil{}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, True{}}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Nil{}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Nil{}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FArr{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SVal{}, +f2}, +outer}} 1n+kk:
      match kk:
        case 0n:
          {==}
        case 1n+jj:
          (2n+gg, {==})
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCom{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SKey{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCom{}, +f1}, Con{Pull.FObj{Pull.SCol{}, +f2}, +outer}} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Nil{} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 0n:
      Unit{}
    case SCon{+c1, +t1} Nil{} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCom{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FArr{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SVal{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SKey{}, False{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, True{}}, +ff} 1n+kk:
      Unit{}
    case SCon{+c1, +t1} Con{Pull.FObj{Pull.SCol{}, False{}}, +ff} 1n+kk:
      Unit{}

# a colon, for both
law lpu_colon:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for ih: @st2: List<&2, Pull.Frame> -> @g2: Nat -> kr(Pull.next.go(1n+fn, tl, Pull.S{Pull.MIdle{}, st2, Pull.GNext{},
    False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{Pull.MIdle{}, st2, Pull.GSkip{dd}, False{}, False{}}),
    dd)
  kr(Pull.next.go(1n+fn, tl, Pull.punct.colon(stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.punct.colon(stack, Pull.GSkip{dd})), dd)

def lpu_colon(tl, fn, stack, dd, gg, ih):
  match stack:
    case Nil{}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SVal{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SCom{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SKey{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SCol{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SVal{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SCom{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SKey{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SCol{}, +f}, +frames}:
      ih(Pull.FObj{Pull.SVal{}, False{}} <> frames, 2n+gg)

# a comma, for both
law lpu_comma:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for ih: @st2: List<&2, Pull.Frame> -> @g2: Nat -> kr(Pull.next.go(1n+fn, tl, Pull.S{Pull.MIdle{}, st2, Pull.GNext{},
    False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{Pull.MIdle{}, st2, Pull.GSkip{dd}, False{}, False{}}),
    dd)
  kr(Pull.next.go(1n+fn, tl, Pull.punct.comma(stack, Pull.GNext{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.punct.comma(stack, Pull.GSkip{dd})), dd)

def lpu_comma(tl, fn, stack, dd, gg, ih):
  match stack:
    case Nil{}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SVal{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SCom{}, +f}, +frames}:
      ih(Pull.FArr{Pull.SVal{}, False{}} <> frames, 2n+gg)
    case Con{Pull.FArr{Pull.SKey{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FArr{Pull.SCol{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SVal{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SCom{}, +f}, +frames}:
      ih(Pull.FObj{Pull.SKey{}, False{}} <> frames, 2n+gg)
    case Con{Pull.FObj{Pull.SKey{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Con{Pull.FObj{Pull.SCol{}, +f}, +frames}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)

# a punctuation token, for both
law ls_punct:
  for +tl: String
  for +fn: Nat
  for +tok: Lex.Tok
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for ih: @st2: List<&2, Pull.Frame> -> @g2: Nat -> kr(Pull.next.go(1n+fn, tl, Pull.S{Pull.MIdle{}, st2, Pull.GNext{},
    False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{Pull.MIdle{}, st2, Pull.GSkip{dd}, False{}, False{}}),
    dd)
  kr(Pull.next.go(1n+fn, tl, Pull.punct.go(tok, stack, Pull.GNext{}, False{})),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.punct.go(tok, stack, Pull.GSkip{dd}, False{})), dd)

def ls_punct(tl, fn, tok, stack, dd, gg, ih):
  match tok:
    case Lex.TOpenArr{}:
      lo_arr(tl, fn, stack, dd, gg, Pull.expect.val.go(stack))
    case Lex.TOpenObj{}:
      lo_obj(tl, fn, stack, dd, gg, Pull.expect.val.go(stack))
    case Lex.TCloseArr{}:
      lc_arr(tl, fn, stack, dd, gg)
    case Lex.TCloseObj{}:
      lc_obj(tl, fn, stack, dd, gg)
    case Lex.TColon{}:
      lpu_colon(tl, fn, stack, dd, gg, ih)
    case Lex.TComma{}:
      lpu_comma(tl, fn, stack, dd, gg, ih)
    case Lex.TStr{_}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Lex.TWord{_}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Lex.TStrS{_, _}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Lex.TWordS{_, _}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Lex.TBad{}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)

# a `"`, for both
law ls_quote:
  for +tl: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  kr(Pull.next.go(1n+fn, tl, Pull.look.quote(stack, Pull.GNext{}, False{}, Pull.expect.str.for(stack, Pull.GNext{},
    False{}))),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.look.quote(stack, Pull.GSkip{dd}, False{}, Pull.expect.str.for(stack,
      Pull.GSkip{dd}, False{}))), dd)

def ls_quote(tl, fn, stack, dd, gg):
  match stack dd:
    case Nil{} 0n:
      ls_str(tl, fn, Pull.MQuote{}, Nil{}, 0n, 2n+gg, {==}, True{}, {==})
    case Nil{} 1n+kk:
      ls_str(tl, fn, Pull.MQuote{}, Nil{}, 1n+kk, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +fr} 0n:
      ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FArr{Pull.SVal{}, f}, fr}, 0n, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FArr{Pull.SVal{}, +f}, +fr} 1n+kk:
      ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FArr{Pull.SVal{}, f}, fr}, 1n+kk, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FArr{Pull.SCom{}, +f}, +fr} 0n:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})), 0n)
    case Con{Pull.FArr{Pull.SCom{}, +f}, +fr} 1n+kk:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)
    case Con{Pull.FArr{Pull.SKey{}, +f}, +fr} 0n:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})), 0n)
    case Con{Pull.FArr{Pull.SKey{}, +f}, +fr} 1n+kk:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)
    case Con{Pull.FArr{Pull.SCol{}, +f}, +fr} 0n:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})), 0n)
    case Con{Pull.FArr{Pull.SCol{}, +f}, +fr} 1n+kk:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)
    case Con{Pull.FObj{Pull.SVal{}, +f}, +fr} 0n:
      ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FObj{Pull.SVal{}, f}, fr}, 0n, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FObj{Pull.SVal{}, +f}, +fr} 1n+kk:
      ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FObj{Pull.SVal{}, f}, fr}, 1n+kk, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FObj{Pull.SCom{}, +f}, +fr} 0n:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})), 0n)
    case Con{Pull.FObj{Pull.SCom{}, +f}, +fr} 1n+kk:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)
    case Con{Pull.FObj{Pull.SKey{}, +f}, +fr} 0n:
      kim_kr(Pull.next.go(1n+fn, tl, Pull.S{Pull.MQuote{}, Con{Pull.FObj{Pull.SKey{}, f}, fr}, Pull.GNext{}, False{},
        False{}}), Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})),
        ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FObj{Pull.SKey{}, f}, fr}, 1n, 2n+gg, {==}, False{}, {==}))
    case Con{Pull.FObj{Pull.SKey{}, +f}, +fr} 1n+kk:
      ls_str(tl, fn, Pull.MQuote{}, Con{Pull.FObj{Pull.SKey{}, f}, fr}, 1n+kk, 2n+gg, {==}, True{}, {==})
    case Con{Pull.FObj{Pull.SCol{}, +f}, +fr} 0n:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{0n})), 0n)
    case Con{Pull.FObj{Pull.SCol{}, +f}, +fr} 1n+kk:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{1n+kk})), 1n+kk)

# one character between tokens, for both
law ls_plan:
  for +tl: String
  for +fn: Nat
  for +ch: Char
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for +cls: Lex.Class
  for ih: @st2: List<&2, Pull.Frame> -> @g2: Nat -> kr(Pull.next.go(1n+fn, tl, Pull.S{Pull.MIdle{}, st2, Pull.GNext{},
    False{}, False{}}), Pull.next.go(1n+fu(tl, g2), tl, Pull.S{Pull.MIdle{}, st2, Pull.GSkip{dd}, False{}, False{}}),
    dd)
  kr(Pull.next.go(1n+fn, tl, Pull.look.plan(ch, stack, Pull.GNext{}, False{}, cls)),
    Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.look.plan(ch, stack, Pull.GSkip{dd}, False{}, cls)), dd)

def ls_plan(tl, fn, ch, stack, dd, gg, cls, ih):
  match cls:
    case Lex.CSpace{}:
      ih(stack, 2n+gg)
    case Lex.CPunct{+tok}:
      ls_punct(tl, fn, tok, stack, dd, gg, ih)
    case Lex.CQuote{}:
      ls_quote(tl, fn, stack, dd, gg)
    case Lex.CBack{}:
      kr_err(fn, tl, Pull.next.go(1n+fu(tl, 2n+gg), tl, Pull.err.st(Pull.GSkip{dd})), dd)
    case Lex.COther{}:
      ls_word0(tl, fn, ch, stack, dd, gg, Pull.expect.val.go(stack))

# a reader's step and a skip at depth dd, from the same place between tokens,
# are in step
law ls_idle:
  for +xx: String
  for +fn: Nat
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  kr(Pull.next.go(1n+fn, xx, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}),
    Pull.next.go(1n+fu(xx, gg), xx, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{dd}, False{}, False{}}), dd)

def ls_idle(xx, fn, stack, dd, gg):
  match xx:
    case SNil{}:
      Unit{}
    case SCon{+ch, +tl}:
      ls_plan(tl, fn, ch, stack, dd, gg, Lex.classify(ch), st2 => g2 => ls_idle(tl, fn, st2, dd, g2))

# no count is not a count
law ms_no:
  for gl: Type
  for +nn: Nat
  for hh: {None{} == Some{nn} : Maybe<&2, Nat>}
  gl

def ms_no(gl, nn, hh):
  M1.no(gl, Equal.cong(Maybe<&2, Nat>, Bool, zz => M3.ms(zz), None{}, Some{nn}, hh))

# one is not two or more
law m1_no:
  for gl: Type
  for +qq: Nat
  for hh: {Some{1n} == Some{2n+qq} : Maybe<&2, Nat>}
  gl

def m1_no(gl, qq, hh):
  M1.no(gl, Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, Nat>, Bool, zz => M3.m1(zz), Some{1n}, Some{2n+qq},
      hh)))

# the count in a count, or 0
def mget(xx: Maybe<&2, Nat>) -> Nat:
  match xx:
    case Some{kk}:
      kk
    case None{}:
      0n

# one more than a count is one more than pp: the count is pp
law om_inv:
  for xx: Maybe<&2, Nat>
  for +pp: Nat
  for hh: {Laws.one_more(xx) == Some{1n+pp} : Maybe<&2, Nat>}
  {xx == Some{pp} : Maybe<&2, Nat>}

def om_inv(xx, pp, hh):
  match xx:
    case Some{+kk}:
      Equal.cong(Nat, Maybe<&2, Nat>, zz => Some{zz}, kk, pp, Equal.cong(Nat, Nat, zz => M2.npred(zz), 1n+kk, 1n+pp,
        Equal.cong(Maybe<&2, Nat>, Nat, zz => mget(zz), Some{1n+kk}, Some{1n+pp}, hh)))
    case None{}:
      ms_no({None{} == Some{pp} : Maybe<&2, Nat>}, 1n+pp, hh)

# a reader whose root is over starts no value
law dt_len:
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for +es: List<&2, D1.Evt>
  for +dd: Nat
  for +uu: Unit
  {Laws.val_len(D1.view(D1.ev_of(Ezjson.next(Pull.Cur{rr, st, True{}, False{}}))) <> es, dd) == None{} : Maybe<&2,
    Nat>}

def dt_len(rr, st, es, dd, uu):
  e = Equal.sym((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{rr, st, True{}, False{}}),
    Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), rr, Pull.S{Pull.MIdle{}, st, Pull.GNext{}, True{},
    False{}}))), next_ob(rr, st, True{}, uu))
  %e : {Laws.val_len(D1.view(D1.ev_of(_)) <> es, dd) == None{} : Maybe<&2, Nat>}
  dto_len(Pull.next.go(1n+cplmu(0n, 32n, uu), rr, Pull.S{Pull.MIdle{}, st, Pull.GNext{}, True{}, False{}}), es, dd,
    dt_go(rr, cplmu(0n, 32n, uu), st))

# a reader and a skip that go on from the same cursor at depth dp
law ko_on:
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +dp: Nat
  for +uu: Unit
  for hk: kr.on(os, rr, st, dn, dp)
  for +hv: {Laws.val_len(D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}), dp) == Some{pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_on(dn, pp, rr, st, os, dp, uu, hk, hv, ih):
  match dn pp:
    case True{} 0n:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(0n, Pull.Cur{rr, st, True{}, False{}}))} : Pull.Out}, 0n, hv)
    case True{} 1n+qq:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, True{}, False{}}))} : Pull.Out}, 1n+qq,
        Equal.trans(Maybe<&2, Nat>, None{},
        Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, True{}, False{}}), dp), Some{1n+qq},
        Equal.sym(Maybe<&2, Nat>, Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, True{}, False{}}), dp), None{},
          dt_len(rr, st, D1.pulled(qq, D1.cur_of(Ezjson.next(Pull.Cur{rr, st, True{}, False{}}))), dp, uu)), hv))
    case False{} +pp2:
      (+gg, e) = hk
      Equal.trans(Pull.Out, os, Pull.next.go(1n+fu(rr, gg), rr, Pull.S{Pull.MIdle{}, st, Pull.GSkip{dp}, False{},
        False{}}), Pull.Fin{(Pull.SSkip{}, D1.nexts(pp2, Pull.Cur{rr, st, False{}, False{}}))}, e,
        ih(rr, st, dp, gg, hv))

# the reader's null event, and the skip at the same depth
law ko_null:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.ENull{}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.ENull{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_null(dd, dn, pp, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's bool event, and the skip at the same depth
law ko_bool:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +b1: Bool
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EBool{b1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EBool{b1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_bool(dd, dn, pp, _b1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's num event, and the skip at the same depth
law ko_num:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +s1: String
  for +n1: U32
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.ENum{s1, n1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.ENum{s1, n1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_num(dd, dn, pp, _s1, _n1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's str event, and the skip at the same depth
law ko_str:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +s1: String
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EStr{s1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EStr{s1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_str(dd, dn, pp, _s1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's strs event, and the skip at the same depth
law ko_strs:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +s1: String
  for +n1: U32
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EStrS{s1, n1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EStrS{s1, n1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_strs(dd, dn, pp, _s1, _n1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's key event, and the skip at the same depth
law ko_key:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +s1: String
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EKey{s1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EKey{s1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_key(dd, dn, pp, _s1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(0n, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 1n, hv)
    case 0n 1n+qq:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 2n+qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's keys event, and the skip at the same depth
law ko_keys:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +s1: String
  for +n1: U32
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EKeyS{s1, n1}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EKeyS{s1, n1}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_keys(dd, dn, pp, _s1, _n1, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(0n, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 1n, hv)
    case 0n 1n+qq:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 2n+qq, hv)
    case 1n+kk 0n:
      ko_on(dn, 0n, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+kk), 0n, hv), ih)
    case 1n+kk 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+kk, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+kk), 1n+qq, hv), ih)

# the reader's ba event, and the skip at the same depth
law ko_ba:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EBeginArr{}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EBeginArr{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_ba(dd, dn, pp, rr, st, os, uu, hk, hv, ih):
  ko_on(dn, pp, rr, st, os, 1n+dd, uu, hk, om_inv(Laws.val_len(D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}), 1n+dd),
    pp, hv), ih)

# the reader's bo event, and the skip at the same depth
law ko_bo:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EBeginObj{}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EBeginObj{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_bo(dd, dn, pp, rr, st, os, uu, hk, hv, ih):
  ko_on(dn, pp, rr, st, os, 1n+dd, uu, hk, om_inv(Laws.val_len(D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}), 1n+dd),
    pp, hv), ih)

# the close of a container, inside the value
law ko_nea:
  for +kk: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.n(os, rr, st, dn, 1n+kk)
  for +hv: {Laws.val_len(D1.view(Pull.EEndArr{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    1n+kk) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_nea(kk, dn, pp, rr, st, os, uu, hk, hv, ih):
  match kk pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+jj 0n:
      ko_on(dn, 0n, rr, st, os, 1n+jj, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+jj), 0n, hv), ih)
    case 1n+jj 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+jj, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+jj), 1n+qq, hv), ih)

# the reader's ea event, and the skip at the same depth
law ko_ea:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EEndArr{}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EEndArr{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_ea(dd, dn, pp, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(0n, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 1n, hv)
    case 0n 1n+qq:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 2n+qq, hv)
    case 1n+kk 0n:
      ko_nea(kk, dn, 0n, rr, st, os, uu, hk, hv, ih)
    case 1n+kk 1n+qq:
      ko_nea(kk, dn, 1n+qq, rr, st, os, uu, hk, hv, ih)

# the close of a container, inside the value
law ko_neo:
  for +kk: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.n(os, rr, st, dn, 1n+kk)
  for +hv: {Laws.val_len(D1.view(Pull.EEndObj{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    1n+kk) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_neo(kk, dn, pp, rr, st, os, uu, hk, hv, ih):
  match kk pp:
    case 0n 0n:
      hk
    case 0n 1n+qq:
      m1_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, qq, hv)
    case 1n+jj 0n:
      ko_on(dn, 0n, rr, st, os, 1n+jj, uu, hk, om_inv(Laws.val_len(D1.pulled(0n, Pull.Cur{rr, st, dn, False{}}),
        1n+jj), 0n, hv), ih)
    case 1n+jj 1n+qq:
      ko_on(dn, 1n+qq, rr, st, os, 1n+jj, uu, hk, om_inv(Laws.val_len(D1.pulled(1n+qq, Pull.Cur{rr, st, dn,
        False{}}), 1n+jj), 1n+qq, hv), ih)

# the reader's eo event, and the skip at the same depth
law ko_eo:
  for +dd: Nat
  for +dn: Bool
  for +pp: Nat
  for +rr: String
  for +st: List<&2, Pull.Frame>
  for os: Pull.Out
  for +uu: Unit
  for hk: kr.e(Pull.EEndObj{}, Pull.Cur{rr, st, dn, False{}}, os, dd)
  for +hv: {Laws.val_len(D1.view(Pull.EEndObj{}) <> D1.pulled(pp, Pull.Cur{rr, st, dn, False{}}),
    dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}

def ko_eo(dd, dn, pp, rr, st, os, uu, hk, hv, ih):
  match dd pp:
    case 0n 0n:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(0n, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 1n, hv)
    case 0n 1n+qq:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(1n+qq, Pull.Cur{rr, st, dn, False{}}))} : Pull.Out}, 2n+qq, hv)
    case 1n+kk 0n:
      ko_neo(kk, dn, 0n, rr, st, os, uu, hk, hv, ih)
    case 1n+kk 1n+qq:
      ko_neo(kk, dn, 1n+qq, rr, st, os, uu, hk, hv, ih)

# a reader's step and a skip's walk in step, one event on
law ko_at:
  for on: Pull.Out
  for os: Pull.Out
  for +pp: Nat
  for +dd: Nat
  for +uu: Unit
  for hk: kr(on, os, dd)
  for +hv: {Laws.val_len(D1.view(D1.ev_of(Pull.next.use(Pull.next.fin(on)))) <> D1.pulled(pp,
    D1.cur_of(Pull.next.use(Pull.next.fin(on)))), dd) == Some{1n+pp} : Maybe<&2, Nat>}
  for ih: @x2: String -> @s2: List<&2, Pull.Frame> -> @d2: Nat -> @g2: Nat -> {Laws.val_len(D1.pulled(pp,
    Pull.Cur{x2, s2, False{}, False{}}), d2) == Some{pp} : Maybe<&2, Nat>} -> {Pull.next.go(1n+fu(x2, g2), x2,
    Pull.S{Pull.MIdle{}, s2, Pull.GSkip{d2}, False{}, False{}}) == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, Pull.Cur{x2,
    s2, False{}, False{}}))} : Pull.Out}
  {os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, D1.cur_of(Pull.next.use(Pull.next.fin(on)))))} : Pull.Out}

def ko_at(on, os, pp, dd, uu, hk, hv, ih):
  match on:
    case Pull.More{+t1, +s1}:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, D1.cur_of(Pull.next.use(Pull.next.fin(Pull.More{t1,
        s1})))))} : Pull.Out}, 1n+pp, hv)
    case Pull.Fin{(Pull.SSkip{}, +cc)}:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SSkip{}, cc)})))))} : Pull.Out}, 1n+pp, hv)
    case Pull.Fin{(Pull.SEv{Pull.EErr{}}, +cc)}:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EErr{}}, cc)})))))} : Pull.Out}, 1n+pp, hv)
    case Pull.Fin{(Pull.SEv{Pull.EEnd{}}, +cc)}:
      ms_no({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EEnd{}}, cc)})))))} : Pull.Out}, 1n+pp, hv)
    case Pull.Fin{(Pull.SEv{Pull.ENull{}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.ENull{}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.ENull{}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_null(dd, dn, pp, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EBool{+b1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EBool{b1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EBool{+b1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_bool(dd, dn, pp, b1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.ENum{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.ENum{s1, n1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.ENum{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_num(dd, dn, pp, s1, n1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EStr{+s1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EStr{s1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EStr{+s1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_str(dd, dn, pp, s1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EStrS{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EStrS{s1, n1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EStrS{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_strs(dd, dn, pp, s1, n1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EKey{+s1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EKey{s1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EKey{+s1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_key(dd, dn, pp, s1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EKeyS{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EKeyS{s1, n1}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EKeyS{+s1, +n1}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_keys(dd, dn, pp, s1, n1, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_ba(dd, dn, pp, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_bo(dd, dn, pp, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EEndArr{}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_ea(dd, dn, pp, rr, st, os, uu, hk, hv, ih)
    case Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, Pull.Cur{+rr, +st, +dn, True{}})}:
      Empty.absurd({os == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp,
        D1.cur_of(Pull.next.use(Pull.next.fin(Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, Pull.Cur{rr, st, dn,
        True{}})})))))} : Pull.Out}, hk)
    case Pull.Fin{(Pull.SEv{Pull.EEndObj{}}, Pull.Cur{+rr, +st, +dn, False{}})}:
      ko_eo(dd, dn, pp, rr, st, os, uu, hk, hv, ih)

# a skip at depth dd from a live cursor drops the events that finish the value:
# its cursor is where as many calls of next leave the reader
law ko_go:
  for +mm: Nat
  for +xx: String
  for +stack: List<&2, Pull.Frame>
  for +dd: Nat
  for +gg: Nat
  for +uu: Unit
  for +hv: {Laws.val_len(D1.pulled(mm, Pull.Cur{xx, stack, False{}, False{}}), dd) == Some{mm} : Maybe<&2, Nat>}
  {Pull.next.go(1n+fu(xx, gg), xx, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{dd}, False{}, False{}})
    == Pull.Fin{(Pull.SSkip{}, D1.nexts(mm, Pull.Cur{xx, stack, False{}, False{}}))} : Pull.Out}

def ko_go(mm, xx, stack, dd, gg, uu, hv):
  match mm:
    case 0n:
      ms_no({Pull.next.go(1n+fu(xx, gg), xx, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{dd}, False{}, False{}})
        == Pull.Fin{(Pull.SSkip{}, Pull.Cur{xx, stack, False{}, False{}})} : Pull.Out}, 0n, hv)
    case 1n+pp:
      e = next_ob(xx, stack, False{}, uu)
      +es = Equal.sym((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{xx, stack, False{}, False{}}),
        Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), xx, Pull.S{Pull.MIdle{}, stack, Pull.GNext{},
        False{}, False{}}))), e)
      %es : {Pull.next.go(1n+fu(xx, gg), xx, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{dd}, False{}, False{}})
        == Pull.Fin{(Pull.SSkip{}, D1.nexts(pp, D1.cur_of(_)))} : Pull.Out}
      ko_at(Pull.next.go(1n+cplmu(0n, 32n, uu), xx, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}),
        Pull.next.go(1n+fu(xx, gg), xx, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{dd}, False{}, False{}}), pp, dd, uu,
        ls_idle(xx, cplmu(0n, 32n, uu), stack, dd, gg),
        Equal.trans(Maybe<&2, Nat>,
          Laws.val_len(D1.view(D1.ev_of(Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), xx,
          Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}))))) <> D1.pulled(pp, D1.cur_of(Pull.next.use(
          Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), xx, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{},
          False{}}))))), dd),
          Laws.val_len(D1.view(D1.ev_of(Ezjson.next(Pull.Cur{xx, stack, False{}, False{}}))) <> D1.pulled(pp,
          D1.cur_of(Ezjson.next(Pull.Cur{xx, stack, False{}, False{}}))), dd), Some{1n+pp},
          Equal.cong((Pull.Ev & Pull.Cur), Maybe<&2, Nat>,
            zz => Laws.val_len(D1.view(D1.ev_of(zz)) <> D1.pulled(pp,
            D1.cur_of(zz)), dd), Pull.next.use(Pull.next.fin(Pull.next.go(1n+cplmu(0n, 32n, uu), xx,
            Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}))), Ezjson.next(Pull.Cur{xx, stack, False{},
            False{}}), es), hv),
        x2 => s2 => d2 => g2 => h2 => ko_go(pp, x2, s2, d2, g2, uu, h2))

# laws/SkipPassesOneValue.bend: the whole budget covers a skip over a short text

# the characters of a text
def slen(txt: String) -> Nat:
  match txt:
    case SNil{}:
      0n
    case SCon{_, tl}:
      1n+slen(tl)

# the budget over a text is twice its characters, on top
law fu_len:
  for +txt: String
  for +acc: Nat
  {fu(txt, acc) == Nat.add(Nat.double(slen(txt)), acc) : Nat}

def fu_len(txt, acc):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, +tl}:
      Equal.trans(Nat, fu(tl, 2n+acc), Nat.add(Nat.double(slen(tl)), 2n+acc), 2n+Nat.add(Nat.double(slen(tl)), acc),
        fu_len(tl, 2n+acc), Equal.trans(Nat, Nat.add(Nat.double(slen(tl)), 2n+acc), 1n+Nat.add(Nat.double(slen(tl)),
        1n+acc), 2n+Nat.add(Nat.double(slen(tl)), acc), M2.nat_add_succ(Nat.double(slen(tl)), 1n+acc), Equal.cong(Nat,
        Nat, zz => 1n+zz, Nat.add(Nat.double(slen(tl)), 1n+acc), 1n+Nat.add(Nat.double(slen(tl)), acc),
        M2.nat_add_succ(Nat.double(slen(tl)), acc))))

# not b is true: b is false
law not_t:
  for +bb: Bool
  for hh: {Bool.not(bb) == True{} : Bool}
  {bb == False{} : Bool}

def not_t(bb, hh):
  match bb:
    case True{}:
      M1.no({True{} == False{} : Bool}, hh)
    case False{}:
      {==}

# a text of at most u characters, one character in: its characters and some
# more are u
law bnd_d:
  for +tl: String
  for +uu32: U32
  for +h1: {Bool.not(U32.is_zero(uu32)) == True{} : Bool}
  for ss: (&ee: Nat -> {Nat.add(slen(tl), ee) == U32.to_nat(U32.sub(uu32, 1)) : Nat})
  (&ee: Nat -> {Nat.add(1n+slen(tl), ee) == U32.to_nat(uu32) : Nat})

def bnd_d(tl, uu32, h1, ss):
  (+ee, he) = ss
  (ee, Equal.trans(Nat, 1n+Nat.add(slen(tl), ee), 1n+U32.to_nat(U32.sub(uu32, 1)), U32.to_nat(uu32), Equal.cong(Nat,
    Nat, zz => 1n+zz, Nat.add(slen(tl), ee), U32.to_nat(U32.sub(uu32, 1)), he), Equal.sym(Nat, U32.to_nat(uu32),
    1n+U32.to_nat(U32.sub(uu32, 1)), M3.u32_dec(uu32, not_t(U32.is_zero(uu32), h1)))))

# bnd_d, once the bound is split
law bnd_c:
  for +tl: String
  for +uu32: U32
  for hb: ({Bool.not(U32.is_zero(uu32)) == True{} : Bool} & {D1.bounded(tl, U32.sub(uu32, 1)) == True{} : Bool})
  for ih: {D1.bounded(tl, U32.sub(uu32, 1)) == True{} : Bool} -> (&ee: Nat -> {Nat.add(slen(tl), ee)
    == U32.to_nat(U32.sub(uu32, 1)) : Nat})
  (&ee: Nat -> {Nat.add(1n+slen(tl), ee) == U32.to_nat(uu32) : Nat})

def bnd_c(tl, uu32, hb, ih):
  (h1, h2) = hb
  bnd_d(tl, uu32, h1, ih(h2))

# a text of at most u characters: its characters and some more are u
law sbnd:
  for +xx: String
  for +uu32: U32
  for hh: {D1.bounded(xx, uu32) == True{} : Bool}
  (&ee: Nat -> {Nat.add(slen(xx), ee) == U32.to_nat(uu32) : Nat})

def sbnd(xx, uu32, hh):
  match xx:
    case SNil{}:
      (U32.to_nat(uu32), {==})
    case SCon{_, +tl}:
      bnd_c(tl, uu32, M1.and_both(Bool.not(U32.is_zero(uu32)), D1.bounded(tl, U32.sub(uu32, 1)), hh),
        h2 => sbnd(tl, U32.sub(uu32, 1), h2))

# a level of budget, once uu is known
def rlu(lvl: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      rl(lvl)

# a level of budget is four times 2^lvl
law rl_pow:
  for +lvl: Nat
  {rl(lvl) == Nat.double(Nat.double(M2.pow2(lvl))) : Nat}

def rl_pow(lvl):
  match lvl:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.add(rl(pp), rl(pp)), Nat.add(Nat.double(Nat.double(M2.pow2(pp))),
        Nat.double(Nat.double(M2.pow2(pp)))), Nat.double(Nat.double(Nat.double(M2.pow2(pp)))), Equal.cong(Nat, Nat,
        +zz => Nat.add(zz, zz), rl(pp), Nat.double(Nat.double(M2.pow2(pp))), rl_pow(pp)), Equal.sym(Nat,
        Nat.double(Nat.double(Nat.double(M2.pow2(pp)))), Nat.add(Nat.double(Nat.double(M2.pow2(pp))),
        Nat.double(Nat.double(M2.pow2(pp)))), M2.nat_double(Nat.double(Nat.double(M2.pow2(pp))))))

# rl_pow, with the level named through uu
law rlu_pow:
  for +lvl: Nat
  for +uu: Unit
  {rlu(lvl, uu) == Nat.double(Nat.double(M2.pow2u(lvl, uu))) : Nat}

def rlu_pow(lvl, uu):
  match uu:
    case Unit{}:
      rl_pow(lvl)

# level 0 is four jumps
law rlu0:
  for +uu: Unit
  {rlu(0n, uu) == 4n : Nat}

def rlu0(uu):
  match uu:
    case Unit{}:
      {==}

# 2^(n + 1) is twice 2^n
law pow2u_s:
  for +nn: Nat
  for +uu: Unit
  {M2.pow2u(1n+nn, uu) == Nat.double(M2.pow2u(nn, uu)) : Nat}

def pow2u_s(_nn, uu):
  match uu:
    case Unit{}:
      {==}

# the budget of levels lvl to lvl + pp, and one more of level lvl, is the level
# after them
law cpl_rl:
  for +pp: Nat
  for +lvl: Nat
  {Nat.add(cpl(pp, lvl), rl(lvl)) == rl(1n+Nat.add(lvl, pp)) : Nat}

def cpl_rl(pp, lvl):
  match pp:
    case 0n:
      Equal.cong(Nat, Nat, +zz => Nat.add(rl(zz), rl(zz)), lvl, Nat.add(lvl, 0n), Equal.sym(Nat, Nat.add(lvl, 0n), lvl,
        M2.nat_add_zero(lvl)))
    case 1n+(+qq):
      Equal.trans(Nat, Nat.add(Nat.add(rl(lvl), cpl(qq, 1n+lvl)), rl(lvl)), Nat.add(cpl(qq, 1n+lvl), rl(1n+lvl)),
        rl(1n+Nat.add(lvl, 1n+qq)), Equal.trans(Nat, Nat.add(Nat.add(rl(lvl), cpl(qq, 1n+lvl)), rl(lvl)),
        Nat.add(rl(lvl), Nat.add(cpl(qq, 1n+lvl), rl(lvl))), Nat.add(cpl(qq, 1n+lvl), rl(1n+lvl)),
        M2.nat_add_assoc(rl(lvl), cpl(qq, 1n+lvl), rl(lvl)), Equal.trans(Nat, Nat.add(rl(lvl), Nat.add(cpl(qq, 1n+lvl),
        rl(lvl))), Nat.add(cpl(qq, 1n+lvl), Nat.add(rl(lvl), rl(lvl))), Nat.add(cpl(qq, 1n+lvl), rl(1n+lvl)),
        M2.nat_add_lcomm(rl(lvl), cpl(qq, 1n+lvl), rl(lvl)), {==})), Equal.trans(Nat, Nat.add(cpl(qq, 1n+lvl),
        rl(1n+lvl)), rl(1n+Nat.add(1n+lvl, qq)), rl(1n+Nat.add(lvl, 1n+qq)), cpl_rl(qq, 1n+lvl), Equal.cong(Nat, Nat,
        zz => rl(1n+zz), 1n+Nat.add(lvl, qq), Nat.add(lvl, 1n+qq), Equal.sym(Nat, Nat.add(lvl, 1n+qq), 1n+Nat.add(lvl,
        qq), M2.nat_add_succ(lvl, qq)))))

# cpl_rl, with the budget named through uu
law cplu_rl:
  for +pp: Nat
  for +lvl: Nat
  for +uu: Unit
  {Nat.add(cplu(lvl, pp, uu), rlu(lvl, uu)) == rlu(1n+Nat.add(lvl, pp), uu) : Nat}

def cplu_rl(pp, lvl, uu):
  match uu:
    case Unit{}:
      cpl_rl(pp, lvl)

# eight times a sum is eight times each part
law ddd_add:
  for +aa: Nat
  for +bb: Nat
  {Nat.double(Nat.double(Nat.double(Nat.add(aa, bb)))) == Nat.add(Nat.double(Nat.double(Nat.double(aa))),
    Nat.double(Nat.double(Nat.double(bb)))) : Nat}

def ddd_add(aa, bb):
  Equal.trans(Nat, Nat.double(Nat.double(Nat.double(Nat.add(aa, bb)))), Nat.double(Nat.double(Nat.add(Nat.double(aa),
    Nat.double(bb)))), Nat.add(Nat.double(Nat.double(Nat.double(aa))), Nat.double(Nat.double(Nat.double(bb)))),
    Equal.cong(Nat, Nat, zz => Nat.double(Nat.double(zz)), Nat.double(Nat.add(aa, bb)), Nat.add(Nat.double(aa),
    Nat.double(bb)), M2.nat_double_add(aa, bb)), Equal.trans(Nat, Nat.double(Nat.double(Nat.add(Nat.double(aa),
    Nat.double(bb)))), Nat.double(Nat.add(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb)))),
    Nat.add(Nat.double(Nat.double(Nat.double(aa))), Nat.double(Nat.double(Nat.double(bb)))), Equal.cong(Nat, Nat,
    zz => Nat.double(zz), Nat.double(Nat.add(Nat.double(aa), Nat.double(bb))), Nat.add(Nat.double(Nat.double(aa)),
    Nat.double(Nat.double(bb))), M2.nat_double_add(Nat.double(aa), Nat.double(bb))),
    M2.nat_double_add(Nat.double(Nat.double(aa)), Nat.double(Nat.double(bb)))))

# eight times is two times and six times
law ddd_split:
  for +aa: Nat
  {Nat.add(Nat.double(aa), Nat.add(Nat.double(Nat.double(aa)),
    Nat.double(aa))) == Nat.double(Nat.double(Nat.double(aa))) : Nat}

def ddd_split(aa):
  Equal.trans(Nat, Nat.add(Nat.double(aa), Nat.add(Nat.double(Nat.double(aa)), Nat.double(aa))),
    Nat.add(Nat.double(aa), Nat.add(Nat.double(aa), Nat.double(Nat.double(aa)))),
    Nat.double(Nat.double(Nat.double(aa))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.double(aa), zz),
    Nat.add(Nat.double(Nat.double(aa)), Nat.double(aa)), Nat.add(Nat.double(aa), Nat.double(Nat.double(aa))),
    M2.nat_add_comm(Nat.double(Nat.double(aa)), Nat.double(aa))), Equal.trans(Nat, Nat.add(Nat.double(aa),
    Nat.add(Nat.double(aa), Nat.double(Nat.double(aa)))), Nat.add(Nat.add(Nat.double(aa), Nat.double(aa)),
    Nat.double(Nat.double(aa))), Nat.double(Nat.double(Nat.double(aa))), Equal.sym(Nat, Nat.add(Nat.add(Nat.double(aa),
    Nat.double(aa)), Nat.double(Nat.double(aa))), Nat.add(Nat.double(aa), Nat.add(Nat.double(aa),
    Nat.double(Nat.double(aa)))), M2.nat_add_assoc(Nat.double(aa), Nat.double(aa), Nat.double(Nat.double(aa)))),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.double(aa), Nat.double(aa)), Nat.double(Nat.double(aa))),
    Nat.add(Nat.double(Nat.double(aa)), Nat.double(Nat.double(aa))), Nat.double(Nat.double(Nat.double(aa))),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.double(aa))), Nat.add(Nat.double(aa), Nat.double(aa)),
    Nat.double(Nat.double(aa)), Equal.sym(Nat, Nat.double(Nat.double(aa)), Nat.add(Nat.double(aa), Nat.double(aa)),
    M2.nat_double(Nat.double(aa)))), Equal.sym(Nat, Nat.double(Nat.double(Nat.double(aa))),
    Nat.add(Nat.double(Nat.double(aa)), Nat.double(Nat.double(aa))), M2.nat_double(Nat.double(Nat.double(aa)))))))

# three more on the right
law add3:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, 3n+bb) == 3n+Nat.add(aa, bb) : Nat}

def add3(aa, bb):
  Equal.trans(Nat, Nat.add(aa, 3n+bb), 1n+Nat.add(aa, 2n+bb), 3n+Nat.add(aa, bb), M2.nat_add_succ(aa, 2n+bb),
    Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(aa, 2n+bb), 2n+Nat.add(aa, bb), Equal.trans(Nat, Nat.add(aa, 2n+bb),
    1n+Nat.add(aa, 1n+bb), 2n+Nat.add(aa, bb), M2.nat_add_succ(aa, 1n+bb), Equal.cong(Nat, Nat, zz => 1n+zz, Nat.add(aa,
    1n+bb), 1n+Nat.add(aa, bb), M2.nat_add_succ(aa, bb)))))

# the whole budget covers two jumps for each character of a text the length of
# a U32, and more
law ar_w:
  for +xx: String
  for +uu32: U32
  for +uu: Unit
  for ss: (&ee: Nat -> {Nat.add(slen(xx), ee) == U32.to_nat(uu32) : Nat})
  (&gg: Nat -> {cplu(0n, 32n, uu) == 1n+fu(xx, gg) : Nat})

def ar_w(xx, uu32, uu, ss):
  (+ee, he) = ss
  +hp = Equal.trans(Nat, 1n+Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))),
    1n+Nat.add(U32.to_nat(uu32), Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))), M2.pow2u(32n, uu), Equal.sym(Nat,
    1n+Nat.add(U32.to_nat(uu32), Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))), 1n+Nat.add(slen(xx), Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))), Equal.trans(Nat, 1n+Nat.add(U32.to_nat(uu32),
        Nat.sub(M2.pow2u(32n,
    uu), 1n+U32.to_nat(uu32))), 1n+Nat.add(Nat.add(slen(xx), ee), Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))),
    1n+Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))), Equal.cong(Nat, Nat,
    zz => 1n+Nat.add(zz, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))), U32.to_nat(uu32), Nat.add(slen(xx), ee),
    Equal.sym(Nat, Nat.add(slen(xx), ee), U32.to_nat(uu32), he)), Equal.cong(Nat, Nat, zz => 1n+zz,
    Nat.add(Nat.add(slen(xx), ee), Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))), Nat.add(slen(xx), Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))), M2.nat_add_assoc(slen(xx), ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))), M2.nat_lt_ex(U32.to_nat(uu32), M2.pow2u(32n, uu), M2.u_bound(uu, uu32)))
  eq1 = Equal.trans(Nat, Nat.add(4n, cplu(0n, 32n, uu)), Nat.add(cplu(0n, 32n, uu), 4n),
    8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), M2.nat_add_comm(4n, cplu(0n, 32n, uu)), Equal.trans(Nat, Nat.add(cplu(0n, 32n, uu), 4n),
    Nat.add(cplu(0n, 32n, uu), rlu(0n, uu)), 8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))), Equal.sym(Nat, Nat.add(cplu(0n, 32n, uu), rlu(0n, uu)),
    Nat.add(cplu(0n, 32n, uu), 4n), Equal.cong(Nat, Nat, zz => Nat.add(cplu(0n, 32n, uu), zz), rlu(0n, uu), 4n,
    rlu0(uu))), Equal.trans(Nat, Nat.add(cplu(0n, 32n, uu), rlu(0n, uu)), rlu(1n+32n, uu),
    8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), cplu_rl(32n, 0n, uu), Equal.trans(Nat, rlu(1n+32n, uu),
    Nat.double(Nat.double(M2.pow2u(1n+32n, uu))), 8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))), rlu_pow(1n+32n, uu), Equal.trans(Nat,
    Nat.double(Nat.double(M2.pow2u(1n+32n, uu))), Nat.double(Nat.double(Nat.double(M2.pow2u(32n, uu)))),
    8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), Equal.cong(Nat, Nat, zz => Nat.double(Nat.double(zz)), M2.pow2u(1n+32n, uu),
    Nat.double(M2.pow2u(32n, uu)), pow2u_s(32n, uu)), Equal.cong(Nat, Nat, zz => Nat.double(Nat.double(Nat.double(zz))),
    M2.pow2u(32n, uu), 1n+Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))),
        Equal.sym(Nat,
    1n+Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))), M2.pow2u(32n, uu), hp)))))))
  eq2 = Equal.trans(Nat, 5n+fu(xx, 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    5n+Nat.add(Nat.double(slen(xx)), 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), Equal.cong(Nat, Nat, zz => 5n+zz, fu(xx,
    3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    Nat.add(Nat.double(slen(xx)), 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))), fu_len(xx,
    3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))))),
        Equal.trans(Nat,
    5n+Nat.add(Nat.double(slen(xx)), 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    8n+Nat.add(Nat.double(slen(xx)), Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), Equal.cong(Nat, Nat, zz => 5n+zz, Nat.add(Nat.double(slen(xx)),
    3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    3n+Nat.add(Nat.double(slen(xx)), Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    add3(Nat.double(slen(xx)), Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))))), Equal.cong(Nat,
    Nat, zz => 8n+zz, Nat.add(Nat.double(slen(xx)), Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))))), Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n,
        uu),
    1n+U32.to_nat(uu32))))))), Equal.trans(Nat, Nat.add(Nat.double(slen(xx)),
    Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))),
    Nat.add(Nat.add(Nat.double(slen(xx)), Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx)))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
    Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.double(slen(xx)), Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx)))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), Nat.add(Nat.double(slen(xx)), Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))))), M2.nat_add_assoc(Nat.double(slen(xx)), Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(slen(xx)),
    Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx)))), Nat.double(Nat.double(Nat.double(Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))), Nat.add(Nat.double(Nat.double(Nat.double(slen(xx)))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
    Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))), Nat.add(Nat.double(slen(xx)), Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx)))), Nat.double(Nat.double(Nat.double(slen(xx)))), ddd_split(slen(xx))), Equal.sym(Nat,
    Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
    Nat.add(Nat.double(Nat.double(Nat.double(slen(xx)))), Nat.double(Nat.double(Nat.double(Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))), ddd_add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32))))))))))
  (3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))),
        M2.nat_add_cancel(4n,
    cplu(0n, 32n, uu), 1n+fu(xx, 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))), Nat.double(slen(xx))),
    Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32)))))))), Equal.trans(Nat,
    Nat.add(4n, cplu(0n, 32n, uu)), 8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee,
    Nat.sub(M2.pow2u(32n, uu), 1n+U32.to_nat(uu32))))))), 5n+fu(xx, 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))))), eq1, Equal.sym(Nat, 5n+fu(xx, 3n+Nat.add(Nat.add(Nat.double(Nat.double(slen(xx))),
    Nat.double(slen(xx))), Nat.double(Nat.double(Nat.double(Nat.add(ee, Nat.sub(M2.pow2u(32n, uu),
    1n+U32.to_nat(uu32)))))))), 8n+Nat.double(Nat.double(Nat.double(Nat.add(slen(xx), Nat.add(ee, Nat.sub(M2.pow2u(32n,
    uu), 1n+U32.to_nat(uu32))))))), eq2))))

# the whole budget covers a text the length of a U32
law ar_u:
  for +xx: String
  for +uu32: U32
  for +uu: Unit
  for hh: {D1.bounded(xx, uu32) == True{} : Bool}
  (&gg: Nat -> {cplu(0n, 32n, uu) == 1n+fu(xx, gg) : Nat})

def ar_u(xx, uu32, uu, hh):
  ar_w(xx, uu32, uu, sbnd(xx, uu32, hh))

# laws/SkipPassesOneValue.bend: the law

# skip on a live cursor over a short text, once the whole budget is known to
# cover it
law pk_w:
  for +xx: String
  for +st: List<&2, Pull.Frame>
  for +mm: Nat
  for +uu: Unit
  for ss: (&gg: Nat -> {cplu(0n, 32n, uu) == 1n+fu(xx, gg) : Nat})
  for +hv: {Laws.val_len(D1.pulled(mm, Pull.Cur{xx, st, False{}, False{}}), 0n) == Some{mm} : Maybe<&2, Nat>}
  {Ezjson.skip(Pull.Cur{xx, st, False{}, False{}}) == D1.nexts(mm, Pull.Cur{xx, st, False{}, False{}}) : Pull.Cur}

def pk_w(xx, st, mm, uu, ss, hv):
  (+gg, ec) = ss
  Equal.trans(Pull.Cur, Ezjson.skip(Pull.Cur{xx, st, False{}, False{}}),
    Pull.skip.use(Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), xx, Pull.S{Pull.MIdle{}, st, Pull.GSkip{0n}, False{},
    False{}}))), D1.nexts(mm, Pull.Cur{xx, st, False{}, False{}}), skip_ob(xx, st, uu),
    Equal.trans(Pull.Cur, Pull.skip.use(Pull.next.fin(Pull.next.go(cplu(0n, 32n, uu), xx, Pull.S{Pull.MIdle{}, st,
      Pull.GSkip{0n}, False{}, False{}}))), Pull.skip.use(Pull.next.fin(Pull.next.go(1n+fu(xx, gg), xx,
      Pull.S{Pull.MIdle{}, st, Pull.GSkip{0n}, False{}, False{}}))), D1.nexts(mm, Pull.Cur{xx, st, False{}, False{}}),
      Equal.cong(Nat, Pull.Cur, zz => Pull.skip.use(Pull.next.fin(Pull.next.go(zz, xx, Pull.S{Pull.MIdle{}, st,
        Pull.GSkip{0n}, False{}, False{}}))), cplu(0n, 32n, uu), 1n+fu(xx, gg), ec),
      Equal.cong(Pull.Out, Pull.Cur, zz => Pull.skip.use(Pull.next.fin(zz)), Pull.next.go(1n+fu(xx, gg), xx,
        Pull.S{Pull.MIdle{}, st, Pull.GSkip{0n}, False{}, False{}}), Pull.Fin{(Pull.SSkip{}, D1.nexts(mm, Pull.Cur{xx,
        st, False{}, False{}}))}, ko_go(mm, xx, st, 0n, gg, uu, hv))))

# skip drops one whole value, the budget named through uu
law pull_skip_u:
  for +cur: Pull.Cur
  for +mm: Nat
  for +uu: Unit
  for +h_s: {D1.short(Laws.rest_of(cur)) == True{} : Bool}
  for +h_v: {Laws.val_len(D1.pulled(mm, cur), 0n) == Some{mm} : Maybe<&2, Nat>}
  {Ezjson.skip(cur) == D1.nexts(mm, cur) : Pull.Cur}

def pull_skip_u(cur, mm, uu, h_s, h_v):
  match cur mm:
    case Pull.Cur{+xx, +st, +dn, True{}} 0n:
      ms_no({Ezjson.skip(Pull.Cur{xx, st, dn, True{}}) == Pull.Cur{xx, st, dn, True{}} : Pull.Cur}, 0n, h_v)
    case Pull.Cur{+xx, +st, +dn, True{}} 1n+pp:
      ms_no({Ezjson.skip(Pull.Cur{xx, st, dn, True{}}) == D1.nexts(1n+pp, Pull.Cur{xx, st, dn, True{}}) : Pull.Cur},
        1n+pp, h_v)
    case Pull.Cur{+xx, +st, True{}, False{}} 0n:
      ms_no({Ezjson.skip(Pull.Cur{xx, st, True{}, False{}}) == Pull.Cur{xx, st, True{}, False{}} : Pull.Cur}, 0n, h_v)
    case Pull.Cur{+xx, +st, True{}, False{}} 1n+pp:
      ms_no({Ezjson.skip(Pull.Cur{xx, st, True{}, False{}}) == D1.nexts(1n+pp, Pull.Cur{xx, st, True{}, False{}})
        : Pull.Cur}, 1n+pp, Equal.trans(Maybe<&2, Nat>, None{}, Laws.val_len(D1.pulled(1n+pp, Pull.Cur{xx, st, True{},
        False{}}), 0n), Some{1n+pp}, Equal.sym(Maybe<&2, Nat>, Laws.val_len(D1.pulled(1n+pp, Pull.Cur{xx, st, True{},
        False{}}), 0n), None{}, dt_len(xx, st, D1.pulled(pp, D1.cur_of(Ezjson.next(Pull.Cur{xx, st, True{},
        False{}}))), 0n, uu)), h_v))
    case Pull.Cur{+xx, +st, False{}, False{}} +m2:
      pk_w(xx, st, m2, uu, ar_u(xx, 4294967295, uu, h_s), h_v)

def Laws.pull_skip(cur, mm, h_s, h_v):
  pull_skip_u(cur, mm, Unit{}, h_s, h_v)

def Laws.pull_skip_next(cur, mm, h_s, h_v):
  Equal.cong(Pull.Cur, Pull.Ev, zz => D1.ev_of(Ezjson.next(zz)), Ezjson.skip(cur), D1.nexts(mm, cur),
    pull_skip_u(cur, mm, Unit{}, h_s, h_v))
