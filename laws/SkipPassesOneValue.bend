# For every cursor whose unread text is shorter than 2^32 characters, at a
# position where a value may start, `next(skip(c))` yields the event that
# follows that value's last event in the full stream from `c`
#
# It carries the same bound as laws/CursorEventsMatchParse.bend: its unread
# text is shorter than 2^32 characters. Without it it fails for texts of about
# 2^35 characters or more: `skip` walks a whole value on one budget of 4 ×
# (2^33 − 1) jumps and spends two on each bare word, so an array of about 2^34
# numbers uses the budget up, and `skip` returns a failed cursor where `next`
# would read on.
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ./defs/CursorAndNumberRules.bend as D1

# the unread suffix of a cursor
def rest_of(cur: Pull.Cur) -> String:
  match cur:
    case Pull.Cur{rest, _, _, _}:
      rest

# one more event than a count, if there is one
def one_more(nn: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match nn:
    case Some{kk}:
      Some{1n+kk}
    case None{}:
      None{}

# how many events finish the value that starts the events, with `depth`
# containers of it already open: Some{n} when the first n events are exactly
# that. None when the events run out first, or an end, a failure, or a close
# or a key where no container of the value is open comes first
def val_len(es: List<&2, D1.Evt>, depth: Nat) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case Con{ev, tl}:
      match ev:
        case D1.VBeginArr{}:
          one_more(val_len(tl, 1n+depth))
        case D1.VBeginObj{}:
          one_more(val_len(tl, 1n+depth))
        case D1.VEndArr{}:
          match depth:
            case 0n:
              None{}
            case 1n+kk:
              match kk:
                case 0n:
                  Some{1n}
                case 1n+jj:
                  one_more(val_len(tl, 1n+jj))
        case D1.VEndObj{}:
          match depth:
            case 0n:
              None{}
            case 1n+kk:
              match kk:
                case 0n:
                  Some{1n}
                case 1n+jj:
                  one_more(val_len(tl, 1n+jj))
        case D1.VKey{_}:
          match depth:
            case 0n:
              None{}
            case 1n+kk:
              one_more(val_len(tl, 1n+kk))
        case D1.VEnd{}:
          None{}
        case D1.VErr{}:
          None{}
        case _:
          match depth:
            case 0n:
              Some{1n}
            case 1n+kk:
              one_more(val_len(tl, 1n+kk))

# LAW: skip drops one whole value: when the first mm events next yields from a
# cursor are exactly one value, skip leaves the cursor where mm calls of next
# leave it
law pull_skip:
  for +cur: Pull.Cur
  for +mm: Nat
  for +h_s: {D1.short(rest_of(cur)) == True{} : Bool}
  for +h_v: {val_len(D1.pulled(mm, cur), 0n) == Some{mm} : Maybe<&2, Nat>}
  {Ezjson.skip(cur) == D1.nexts(mm, cur) : Pull.Cur}

# LAW: after skip, next yields the event that follows the value's last event
# in the events from the same cursor
law pull_skip_next:
  for +cur: Pull.Cur
  for +mm: Nat
  for +h_s: {D1.short(rest_of(cur)) == True{} : Bool}
  for +h_v: {val_len(D1.pulled(mm, cur), 0n) == Some{mm} : Maybe<&2, Nat>}
  {D1.ev_of(Ezjson.next(Ezjson.skip(cur))) == D1.ev_of(Ezjson.next(D1.nexts(mm, cur))) : Pull.Ev}
