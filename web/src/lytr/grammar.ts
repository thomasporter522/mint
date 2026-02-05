import type { Ranged } from './utils';

export type Atom = 
  | { type: 'Hole' }
  | { type: 'Identifier', value: string }

export type PrimaryToken =
  | { type: 'BOF' } // beginning of file
  | { type: 'EOF' } // end of file
  | { type: 'TOP' } // open parens
  | { type: 'TCP' } // close parens
  | { type: 'TAtom', atom: Atom }
  | { type: 'TColon' }
  | { type: 'TPostulate' }
  | { type: 'TChecker' }
  | { type: 'TConstruct' }
  | { type: 'TEnd' }

export type SecondaryToken =
  | { type: 'Whitespace', value: string }
  | { type: 'Unlexed', value: string };

export type Token =
  | { type: 'Primary', token: PrimaryToken }
  | { type: 'Secondary', token: SecondaryToken };

export type Precedence = 
  | { type: 'Interior' } // never relevant, always matches over
  | { type: 'Uninterested' } // can't have a child
  | { type: 'Precedence', value: number };

export function getPrecedence(token: PrimaryToken): [Precedence, Precedence] {
  switch (token.type) {
    case 'BOF': return [{ type: 'Uninterested' }, { type: 'Interior' }];
    case 'EOF': return [{ type: 'Interior' }, { type: 'Uninterested' }];
    case 'TOP': return [{ type: 'Uninterested' }, { type: 'Interior' }];
    case 'TCP': return [{ type: 'Interior' }, { type: 'Uninterested' }];
    case 'TAtom': return [{ type: 'Uninterested' }, { type: 'Uninterested' }];
    case 'TColon': return [{ type: 'Precedence', value: 1.0 }, { type: 'Precedence', value: 1.1 }];
    // case 'TPostulate': return [{ type: 'Uninterested' }, { type: 'Precedence', value: 0.0 }];
    // case 'TChecker': return [{ type: 'Uninterested' }, { type: 'Precedence', value: 0.0 }];
    // case 'TConstruct': return [{ type: 'Uninterested' }, { type: 'Precedence', value: 0.0 }];
    case 'TPostulate': return [{ type: 'Uninterested' }, { type: 'Uninterested' }];
    case 'TChecker': return [{ type: 'Uninterested' }, { type: 'Uninterested' }];
    case 'TConstruct': return [{ type: 'Uninterested' }, { type: 'Uninterested' }];
    case 'TEnd': return [{ type: 'Interior' }, { type: 'Uninterested' }];
    default: return [{ type: 'Uninterested' }, { type: 'Uninterested' }]; 
  }
}

// Match morph: a mechanism to prevent things like [0,1,2) from being parsed.
// The basic format here is to specify which tokens match which.
// But [ matches , and , matched ), so how do we prevent the aforementioned nonsense?
// When [ matches , then that comma gets morphed into a "list comma", which looks the
// same but allows it to distinguish itself from the tuple comma and refuse to match ).
// This solution is a little strange but it's extremely lightweight and allows the
// normal case to remain unchanged (you can just use the Match constructor below most
// of the time) so I think it's good.

export type MatchTokenResult = 
  | { type: 'Match' }
  | { type: 'MatchMorph', token: PrimaryToken }
  | { type: 'NoMatch' };

function isBlockToken(t : PrimaryToken) : boolean {
  return (t.type === 'TPostulate' || t.type === 'TChecker' || t.type === 'TConstruct')
}

export function matchToken(te1: PrimaryToken, te2: PrimaryToken): MatchTokenResult {
  const t1 = te1.type;
  const t2 = te2.type;
  
  if (t1 === 'BOF' && t2 === 'EOF') return { type: 'Match' };
  if (t1 === 'TOP' && t2 === 'TCP') return { type: 'Match' };
  // if (t1 === 'TOP' && t2 === 'TColon') return { type: 'Match' };
  // if (t1 === 'TColon' && t2 === 'TCP') return { type: 'Match' };
  if (isBlockToken(te1) && isBlockToken(te2)) return { type: 'Match' };
  if (isBlockToken(te1) && t2 === 'TEnd') return { type: 'Match' };
  
  return { type: 'NoMatch' }; // fallthrough
}

export function isValidStart(token: PrimaryToken): boolean {
  const [leftPrec, _] = getPrecedence(token);
  return leftPrec.type !== 'Interior';
}

export function isValidEnd(token: Ranged<PrimaryToken>): boolean {
  const [_, rightPrec] = getPrecedence(token.value);
  return rightPrec.type !== 'Interior';
}