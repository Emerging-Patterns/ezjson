# proofs of laws/LexersAgree.bend
import Base
import ../src/lex.bend as Lex
import ../laws/LexersAgree.bend as Laws
import ./lemmas/CharacterClasses.bend as M1
import ./lemmas/LexemeOrder.bend as M2

# the lemmas' span read-out is the law's, token by token
law den_same:
  for +tok: Lex.Tok
  {M2.den(tok) == Laws.tok.den(tok) : Lex.Tok}

def den_same(tok):
  match tok:
    case Lex.TOpenArr{}:
      {==}
    case Lex.TCloseArr{}:
      {==}
    case Lex.TOpenObj{}:
      {==}
    case Lex.TCloseObj{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TComma{}:
      {==}
    case Lex.TStr{s}:
      {==}
    case Lex.TWord{raw}:
      {==}
    case Lex.TStrS{cut, nn}:
      {==}
    case Lex.TWordS{cut, nn}:
      {==}
    case Lex.TBad{}:
      {==}

# and over a list
law dens_same:
  for +toks: List<&2, Lex.Tok>
  {M2.dens(toks) == Laws.toks.den(toks) : List<&2, Lex.Tok>}

def dens_same(toks):
  match toks:
    case Nil{}:
      {==}
    case hd <> tl:
      %dens_same(tl) : {M2.den(hd) <> M2.dens(tl) == Laws.tok.den(hd) <> _ : List<&2, Lex.Tok>}
      %den_same(hd) : {M2.den(hd) <> M2.dens(tl) == _ <> M2.dens(tl) : List<&2, Lex.Tok>}
      {==}

def Laws.lexers_agree(txt, h_s):
  %dens_same(Lex.tokens(txt)) : {_ == Laws.toks.den(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
    []}))) : List<&2, Lex.Tok>}
  %dens_same(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))) : {M2.dens(Lex.tokens(txt)) == _ :
    List<&2, Lex.Tok>}
  M1.lexers_agree(txt, h_s)
