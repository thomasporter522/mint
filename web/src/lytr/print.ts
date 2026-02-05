import type { Term, Binop, Unop } from './term';
import type { PrimaryToken, Atom } from './grammar';


function printAtom(atom: Atom): string {
  switch (atom.type) {
    case 'Hole': return "?";
    case 'Numlit': return atom.value;
    case 'Identifier': return atom.value;
    case 'TL': return "L";
    case 'TR': return "R";
    default: return '';
  }
}

function printPrimaryToken(token: PrimaryToken): string {
  switch (token.type) {
    case 'BOF':
    case 'EOF': return ''; // Don't print BOF/EOF markers
    case 'TOP': return '(';
    case 'TCP': return ')';
    case 'TAtom': return printAtom(token.atom);
    case 'TArrow': return '->';
    case 'TMapsTo': return '↦';
    case 'TAnd': return 'and';
    case 'TFst': return 'fst';
    case 'TSnd': return 'snd';
    case 'TOr': return 'or';
    case 'TCase': return 'case';
    case 'TPipe': return '|';
    case 'TDoubleArrow': return '=>';
    case 'TEnd': return 'end';
    case 'TTheorem': return 'theorem';
    case 'TColon': return ':';
    case 'TAssign': return ':=';
    case 'TComma': return ',';
    default: return '';
  }
}

function innerPrintTerm(term: Term): string {
  switch (term.value.type) {
    case 'Shard': return printPrimaryToken(term.value.token);
    case 'Multi': return term.value.terms.map(printTerm).join(" ");
    case 'Pair': return '(' + printTerm(term.value.left) + "," + printTerm(term.value.right) + ')';
    case 'Hole': return term.value.inserted ? "" : "?";
    case 'Numlit': return term.value.value;
    case 'Identifier': return term.value.value;
    case 'InfixBinop': return printTerm(term.value.left) + printBinop(term.value.binop) + printTerm(term.value.right);
    case 'PrefixUnop': return printUnop(term.value.unop) + printTerm(term.value.right);
    case 'PostfixUnop': return printTerm(term.value.left) + printUnop(term.value.unop);
    case 'Ap': return printTerm(term.value.fun) + '(' + printTerm(term.value.arg) + ")";
    case 'Case': return printTerm(term.value.scrutinee) + 
             term.value.cases.map(([pattern, body]) => printTerm(pattern) + printTerm(body)).join('');
    case 'Theorem': return "theorem" + printTerm(term.value.pat) + " : " + printTerm(term.value.prop) + " := " + printTerm(term.value.body);
    case 'BUILDER ERROR': return "<BUILDER ERROR>";
  }
}

export function printTerm(term: Term): string {
  const inner = innerPrintTerm(term);
  return term.meta.parens ? "(" + inner + ")" : inner
}

function printBinop(binop: Binop): string {
  switch (binop.type) {
    case 'Arrow': return ' -> ';
    case 'And': return ' and ';
    case 'Or': return ' or ';
    case 'Fun': return ' ↦ ';
    default: return '';
  }
}

function printUnop(unop: Unop): string {
  switch (unop.type) {
    case 'Fst': return '.fst';
    case 'Snd': return '.snd';
    case 'L': return 'L';
    case 'R': return 'R';
    default: return '';
  }
}