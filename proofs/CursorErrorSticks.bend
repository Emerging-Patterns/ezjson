# proofs of laws/CursorErrorSticks.bend
import Base
import ../src/pull.bend as Pull
import ../laws/CursorErrorSticks.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1

def Laws.pull_failed_next(_rest, _stack, _done):
  {==}

# use_err, once the step's stop is in hand
law use_err.at:
  for stop: Pull.Stop
  for cc: Pull.Cur
  for h_err: {Laws.is_err(D1.ev_of(Pull.next.use((stop, cc)))) == True{} : Bool}
  {D1.failed(D1.cur_of(Pull.next.use((stop, cc)))) == True{} : Bool}

def use_err.at(stop, cc, h_err):
  match stop:
    case Pull.SSkip{}:
      {==}
    case Pull.SEv{Pull.ENull{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.ENull{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EBool{aa}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBool{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.ENum{aa, bb}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.ENum{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EStr{aa}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EStr{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EStrS{aa, bb}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EStrS{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EKey{aa}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EKey{aa}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EKeyS{aa, bb}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EKeyS{aa, bb}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EBeginArr{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginArr{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EEndArr{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EEndArr{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EBeginObj{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EBeginObj{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EEndObj{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EEndObj{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EEnd{}}:
      Empty.absurd({D1.failed(D1.cur_of(Pull.next.use((Pull.SEv{Pull.EEnd{}}, cc)))) == True{} : Bool},
        M1.false_true(h_err))
    case Pull.SEv{Pull.EErr{}}:
      {==}

# an error from a step comes with the failed cursor
law use_err:
  for got: (Pull.Stop & Pull.Cur)
  for h_err: {Laws.is_err(D1.ev_of(Pull.next.use(got))) == True{} : Bool}
  {D1.failed(D1.cur_of(Pull.next.use(got))) == True{} : Bool}

def use_err(got, h_err):
  (stop, cc) = got
  use_err.at(stop, cc, h_err)

def Laws.pull_err_fails(cur, h_err):
  match cur:
    case Pull.Cur{rest, stack, done, bad}:
      match bad:
        case True{}:
          {==}
        case False{}:
          use_err(Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}), h_err)
