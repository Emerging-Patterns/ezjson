# `text(ev)` is `Some` of the decoded characters for a string or key event,
# span or owned, and of the spelling for a number event, and `None` for every
# other event
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ./defs/CursorAndNumberRules.bend as D1

# a string, a key, or a number event, span or owned: the events with text
def has_text(ev: Pull.Ev) -> Bool:
  match ev:
    case Pull.EStr{_}:
      True{}
    case Pull.EStrS{_, _}:
      True{}
    case Pull.EKey{_}:
      True{}
    case Pull.EKeyS{_, _}:
      True{}
    case Pull.ENum{_, _}:
      True{}
    case _:
      False{}

# LAW: text of an owned string is its characters
law text_str:
  for body: String
  {Ezjson.text(Pull.EStr{body}) == Some{body} : Maybe<&2, String>}

# LAW: text of an owned key is its characters
law text_key:
  for body: String
  {Ezjson.text(Pull.EKey{body}) == Some{body} : Maybe<&2, String>}

# LAW: text of a string span is the first nn characters of its source
law text_str_span:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.EStrS{src, nn}) == Some{D1.take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of a key span is the first nn characters of its source
law text_key_span:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.EKeyS{src, nn}) == Some{D1.take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of a number is the first nn characters of its source, its spelling
law text_num:
  for +src: String
  for +nn: U32
  {Ezjson.text(Pull.ENum{src, nn}) == Some{D1.take(src, U32.to_nat(nn))} : Maybe<&2, String>}

# LAW: text of every other event is none
law text_none:
  for +ev: Pull.Ev
  for h_kind: {has_text(ev) == False{} : Bool}
  {Ezjson.text(ev) == None{} : Maybe<&2, String>}
