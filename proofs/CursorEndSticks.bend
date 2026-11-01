# proofs of laws/CursorEndSticks.bend
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ../laws/CursorEndSticks.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1

# an end from a step comes with an ended cursor, once the stop is in hand
law use_end.at:
  for stop: Pull.Stop
  for cc: Pull.Cur
  for h_end: {D1.is_end(D1.ev_of(Pull.next.use((stop, cc)))) == True{} : Bool}
  {D1.ended(D1.cur_of(Pull.next.use((stop, cc)))) == True{} : Bool}

def use_end.at(stop, cc, h_end):
  match stop:
    case Pull.SSkip{}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SSkip{}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.ENull{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.ENull{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EBool{aa}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBool{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.ENum{aa, bb}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.ENum{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EStr{aa}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EStr{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EStrS{aa, bb}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EStrS{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EKey{aa}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EKey{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EKeyS{aa, bb}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EKeyS{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EBeginArr{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginArr{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EEndArr{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EEndArr{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EBeginObj{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginObj{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EEndObj{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EEndObj{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))
    case Pull.SEv{Pull.EEnd{}}:
      match cc:
        case Pull.Cur{_, _, _, _}:
          {==}
    case Pull.SEv{Pull.EErr{}}:
      Empty.absurd({D1.ended(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EErr{}}, cc)))) == True{} : Bool},
        M1.false_true(h_end))

# an end from a step comes with an ended cursor
law use_end:
  for got: (Pull.Stop & Pull.Cur)
  for h_end: {D1.is_end(D1.ev_of(Pull.next.use(got))) == True{} : Bool}
  {D1.ended(D1.cur_of(Pull.next.use(got))) == True{} : Bool}

def use_end(got, h_end):
  (stop, cc) = got
  use_end.at(stop, cc, h_end)

def Laws.pull_end_ends(cur, h_end):
  match cur:
    case Pull.Cur{rest, stack, done, bad}:
      match bad:
        case True{}:
          Empty.absurd({D1.ended(D1.cur_of(Ezjson.next(Pull.Cur{rest, stack, done, True{}}))) == True{} : Bool},
            M1.false_true(h_end))
        case False{}:
          use_end(Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}), h_end)

def Laws.pull_ended_next(_stack):
  {==}
