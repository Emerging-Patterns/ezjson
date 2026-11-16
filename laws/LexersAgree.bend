# For texts shorter than 2^32 - 1 characters: the span scanner `tokens`, the
# lexer `parse` reads, gives the tokens the character machine `run` gives from
# the idle state, once every span is read out into the characters it covers.
# The character machine is the lexer said one character at a time; the span
# scanner is the fast path, which keeps spans of the source instead of
# copying them. Internal: a law about the lexer holds it in place without
# making it interface
import Base
import ../src/value.bend as V
import ../src/lex.bend as Lex
import ./defs/CursorAndNumberRules.bend as D1

# a token with its span read out into the characters it covers
def tok.den(tok: Lex.Tok) -> Lex.Tok:
  match tok:
    case Lex.TStrS{cut, +nn}:
      Lex.TStr{V.span.str(cut, nn, U32.is_zero(nn))}
    case Lex.TWordS{cut, +nn}:
      Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))}
    case other:
      other

# tokens with their spans read out
def toks.den(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case hd <> tl:
      tok.den(hd) <> toks.den(tl)

# LAW: the span scanner and the character machine give the same tokens
law lexers_agree:
  for +txt: String
  for h_s: {D1.short(txt) == True{} : Bool}
  {toks.den(Lex.tokens(txt)) == toks.den(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) :
    List<&2, Lex.Tok>}
