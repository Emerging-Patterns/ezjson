# For texts shorter than 2^32 - 1 characters: for every text `t` with
# `parse(t) == Some{j}`, `print(j)` holds no whitespace outside strings, and
# `print(j) == print(j2)` where `parse(print(j)) == Some{j2}`
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# a parse result printed; none when parsing failed
def print_m(mb: Maybe<&2, V.Json>) -> Maybe<&2, String>:
  match mb:
    case None{}:
      None{}
    case Some{jj}:
      Some{Ezjson.print(jj)}

# where a scan of JSON text is: outside strings, inside one, just after a
# backslash inside one, or past whitespace outside strings. RFC 8259 §7: a
# string runs from a quotation mark to the next one no backslash escapes
type Tx is Data:
  TxOut{}
  TxIn{}
  TxEsc{}
  TxWs{}

# one character of the scan
def tx.step(st: Tx, +ch: Char) -> Tx:
  match st:
    case TxOut{}:
      Bool.pick(Tx, D1.is_cp(ch, 34), TxIn{}, Bool.pick(Tx, D1.is_ws(ch), TxWs{}, TxOut{}))
    case TxIn{}:
      Bool.pick(Tx, D1.is_cp(ch, 92), TxEsc{}, Bool.pick(Tx, D1.is_cp(ch, 34), TxOut{}, TxIn{}))
    case TxEsc{}:
      TxIn{}
    case TxWs{}:
      TxWs{}

# the scan of every character, in order
def tx.run(cs: List<&2, Char>, st: Tx) -> Tx:
  match cs:
    case Nil{}:
      st
    case Con{hd, tl}:
      tx.run(tl, tx.step(st, hd))

# whether a scan never met whitespace outside strings
def tx.ok(st: Tx) -> Bool:
  match st:
    case TxWs{}:
      False{}
    case _:
      True{}

# whether a text holds no whitespace outside its strings
def ws_free(txt: String) -> Bool:
  tx.ok(tx.run(String.to_list(txt), TxOut{}))

# LAW: a parsed value prints with no whitespace outside strings
law print_compact:
  for +txt: String
  for +jj: V.Json
  for e_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  {ws_free(Ezjson.print(jj)) == True{} : Bool}

# LAW: a parsed value printed, parsed again and printed again, prints the same
law print_stable:
  for +txt: String
  for +jj: V.Json
  for e_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  for h_s: {D1.short(Ezjson.print(jj)) == True{} : Bool}
  {print_m(Ezjson.parse(Ezjson.print(jj))) == Some{Ezjson.print(jj)} : Maybe<&2, String>}
