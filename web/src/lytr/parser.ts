import type { Ranged } from './utils';
import { mapRanged } from './utils';
import type { Token, PrimaryToken, SecondaryToken } from './grammar';
import { getPrecedence, matchToken, isValidStart, isValidEnd } from './grammar';

export type ShardMode = 'ShardsObstructive' | 'ShardsSecondary';

const shardMode: ShardMode = 'ShardsObstructive';

// Arrays that grow on the right - preserving textual order
// Helper functions to maintain the same semantics as right-growing lists

export type Unform = 
  | { type: 'Secondary', token: Ranged<SecondaryToken> }
  | { type: 'Shard', token: Ranged<PrimaryToken> };

// Syntax forms along with secondary syntax and unmatched tokens (shards)
export type Sharded<T> = 
  | { type: 'Unform', unform: Unform }
  | { type: 'Form', form: T };

// A "work in progress" matched syntactic form
export type PartialForm = 
  | { type: 'Head', token: Ranged<PrimaryToken> }
  | { type: 'Match', form: PartialForm, items: Sharded<PartialForm>[], token: Ranged<PrimaryToken> };

function faceOfPartialForm(pf: PartialForm): Ranged<PrimaryToken> {
  switch (pf.type) {
    case 'Head':
      return pf.token;
    case 'Match':
      return pf.token;
  }
}

/* MATCHING PHASE */
// In this phase, matching relationships are established between tokens.
// Precedence is not brought into play yet. The main function is matchParse

function shatterPartialForm(pf: PartialForm): Sharded<PartialForm>[] {
  switch (pf.type) {
    case 'Head':
      return [{ type: 'Unform', unform: { type: 'Shard', token: pf.token } }];
    case 'Match':
      return [...shatterPartialForm(pf.form), ...pf.items, { type: 'Unform', unform: { type: 'Shard', token: pf.token } }];
  }
}

// This flattens a partial form that appeared on the stack
// It is called when a match has been found that spans over the form,
// and as such the partial form has no further chance to be extended.
// So if it's complete, it stays itself. Otherwise, it is shattered into its constituents.
function flattenPartialForm(f: PartialForm): Sharded<PartialForm>[] {
  return isValidEnd(faceOfPartialForm(f)) 
    ? [{ type: 'Form', form: f }] 
    : shatterPartialForm(f);
}

// Flattening a stack involves flattening all partial forms on the stack
function flatten(spfs: Sharded<PartialForm>[]): Sharded<PartialForm>[] {
  const result: Sharded<PartialForm>[] = [];
  for (const spf of spfs) {
    switch (spf.type) {
      case 'Unform':
        result.push(spf);
        break;
      case 'Form':
        result.push(...flattenPartialForm(spf.form));
        break;
    }
  }
  return result;
}

type MatchStackResult = 
  | { type: 'NoMatch' }
  | { type: 'Match', stack: Sharded<PartialForm>[] };

// This is where a token searches for a match on the stack.
// It also keeps an accumulator of the part of the stack that has
// been skipped over during this search.
// If a match is found, the skipped part is "flattened" and
// placed between the new betrothed couple in the new extended partial form.
function matchStack(
  s: Sharded<PartialForm>[], 
  t: Ranged<PrimaryToken>, 
  sSkipped: Sharded<PartialForm>[]
): MatchStackResult {
  // Process from right to left (since we grow on the right)
  for (let i = s.length - 1; i >= 0; i--) {
    const current = s[i];
    const rest = s.slice(0, i);
    
    switch (current.type) {
      case 'Unform':
        sSkipped.unshift(current);
        continue;
      case 'Form':
        const matchResult = matchToken(faceOfPartialForm(current.form).value, t.value);
        switch (matchResult.type) {
          case 'NoMatch':
            sSkipped.unshift(current);
            continue;
          case 'MatchMorph':
            const newForm1 = { type: 'Match' as const, form: current.form, items: flatten(sSkipped), token: {value:matchResult.token, start: t.start, end:t.end} };
            return { type: 'Match', stack: [...rest, { type: 'Form', form: newForm1 }] };
          case 'Match':
            const newForm2 = { type: 'Match' as const, form: current.form, items: flatten(sSkipped), token: t };
            return { type: 'Match', stack: [...rest, { type: 'Form', form: newForm2 }] };
        }
    }
  }
  return { type: 'NoMatch' };
}

function getPrimaryToken(t : Ranged<Token>) : Ranged<PrimaryToken> {
  return mapRanged((x : Token) => x.token, t)
}

function getSecondaryToken(t : Ranged<Token>) : Ranged<SecondaryToken> {
  return mapRanged((x : Token) => x.token, t)
}

// The stack is a list of partial forms (or shards or secondary)
// Tokens are pushed on one after another onto the right
// Tokens look for a match on the stack.
// If one is not found, it becomes a shard.
// If one is found, it fuses to that form, rolling up the intermediate stack segment.
function matchPush(s: Sharded<PartialForm>[], t: Ranged<Token>): Sharded<PartialForm>[] {
  switch (t.value.type) {
    case 'Secondary':
      return [...s, { type: 'Unform', unform: { type: 'Secondary', token: getSecondaryToken(t) } }];
    case 'Primary':
      const matchResult = matchStack(s, getPrimaryToken(t), []);
      switch (matchResult.type) {
        case 'Match':
          return matchResult.stack;
        case 'NoMatch':
          if (isValidStart(t.value.token)) {
            return [...s, { type: 'Form', form: { type: 'Head', token: getPrimaryToken(t) } }];
          } else {
            return [...s, { type: 'Unform', unform: { type: 'Shard', token: getPrimaryToken(t) } }];
          }
        default:
          // This should never happen due to exhaustive matching above
          return s;
      }
  }
}

function matchPushes(s: Sharded<PartialForm>[], ts: Ranged<Token>[]): Sharded<PartialForm>[] {
  let result = s;
  for (const t of ts) {
    result = matchPush(result, t);
  }
  return result;
}

function matchParse(ts: Ranged<Token>[]): Sharded<PartialForm>[] {
  const tokens: Ranged<Token>[] = [
    { value: { type: 'Primary', token: { type: 'BOF' } }, start:-1, end:-1 },
    ...ts,
    { value: { type: 'Primary', token: { type: 'EOF' } }, start:-1, end:-1 }
  ];
  const result = matchPushes([], tokens);
  
  // Check for the expected structure: should be a single Form with Match(Head(BOF), items, EOF)
  if (result.length === 1 && result[0].type === 'Form') {
    const form = result[0].form;
    if (form.type === 'Match' && 
        form.form.type === 'Head' && 
        form.form.token.value.type === 'BOF' && 
        form.token.value.type === 'EOF') {
      return form.items;
    }
  }
  
  throw new Error('Impossible matching - parser failed to create expected BOF...EOF structure');
}

/* OPERATORIZE PHASE */

// In this phase, operator precedence is used to give matched forms
// their left and right children: their open children, as opposed to
// their closed children which lie between matched tokens of the form.

// It is a "shift-reduce-roll" parser, with that last option indicating
// that neither of the compared faces can take the other as a child,
// and that the two pieces must simply stay at arms length in a
// "multiterm" - a list of terms that occupy the same closed child position.

export type Unforms = Unform[];

// A complete matched syntactic form
export type ClosedForm = 
  | { type: 'Head', token: Ranged<PrimaryToken> }
  | { type: 'Match', form: ClosedForm, items: Sharded<OpenForm>[], token: Ranged<PrimaryToken> };

// A complete matched syntactic form with (possible) children on the left and right
export type OpenForm = {
  type: 'OForm',
  left: OpenForm | null,
  leftUnforms: Unforms,
  closedForm: ClosedForm,
  rightUnforms: Unforms,
  right: OpenForm | null
};

// A complete matched syntactic form with a (possible) child on the left
type HalfOpenForm = {
  type: 'HOForm',
  left: OpenForm | null,
  leftUnforms: Unforms,
  closedForm: ClosedForm,
  rightUnforms: Unforms
};

function headOf(cf: ClosedForm): Ranged<PrimaryToken> {
  switch (cf.type) {
    case 'Head':
      return cf.token;
    case 'Match':
      return headOf(cf.form);
  }
}

function faceOfForm(cf: ClosedForm): Ranged<PrimaryToken> {
  switch (cf.type) {
    case 'Head':
      return cf.token;
    case 'Match':
      return cf.token;
  }
}

function faceOfHalfOpenForm(hof: HalfOpenForm): Ranged<PrimaryToken> {
  return faceOfForm(hof.closedForm);
}

type CompareTokensResult = 
  | { type: 'Shift' } // first thing wants the second as a child
  | { type: 'Reduce' } // second thing wants the first as a child
  | { type: 'Roll' }; // neither can be the other's child

// Precondition: t1 ends a form and t2 starts a form
function compareTokens(t1: PrimaryToken, t2: PrimaryToken): CompareTokensResult {
  const [, rightPrec1] = getPrecedence(t1);
  const [leftPrec2,] = getPrecedence(t2);
  
  if (rightPrec1.type === 'Precedence' && leftPrec2.type === 'Precedence') {
    if (rightPrec1.value < leftPrec2.value) {
      return { type: 'Shift' };
    } else if (rightPrec1.value > leftPrec2.value) {
      return { type: 'Reduce' };
    } else {
      throw new Error('Precedence collision');
    }
  }
  
  if (rightPrec1.type === 'Uninterested' && leftPrec2.type === 'Precedence') {
    return { type: 'Reduce' };
  }
  
  if (rightPrec1.type === 'Precedence' && leftPrec2.type === 'Uninterested') {
    return { type: 'Shift' };
  }
  
  if (rightPrec1.type === 'Uninterested' && leftPrec2.type === 'Uninterested') {
    return { type: 'Roll' };
  }
  
  // Interior cases should never happen according to precondition
  throw new Error('Precondition violated: Interior precedence found');
}

// Need only consider when t starts a form
function wantsLeftChild(t: PrimaryToken): boolean {
  const [leftPrec,] = getPrecedence(t);
  return leftPrec.type === 'Precedence';
}

type OpState = {
  completed: Sharded<OpenForm>[],
  halfOpen: HalfOpenForm[]
};

function opStateRoll(s: OpState, acc: OpenForm | null): Sharded<OpenForm>[] {
  if (s.halfOpen.length === 0 && acc === null) {
    return s.completed;
  }
  
  if (s.halfOpen.length === 0 && acc !== null) {
    return [...s.completed, { type: 'Form', form: acc }];
  }
  
  // Process from right to left since we grow on the right
  const lastHalf = s.halfOpen[s.halfOpen.length - 1];
  const restHalfs = s.halfOpen.slice(0, -1);
  
  if (acc === null) {
    const se2Prime = lastHalf.rightUnforms.map(f => ({ type: 'Unform' as const, unform: f }));
    const accPrime: OpenForm = {
      type: 'OForm',
      left: lastHalf.left,
      leftUnforms: lastHalf.leftUnforms,
      closedForm: lastHalf.closedForm,
      rightUnforms: [],
      right: null
    };
    const rolled = opStateRoll({ completed: s.completed, halfOpen: restHalfs }, accPrime);
    return [...rolled, ...se2Prime];
  } else {
    const newAcc: OpenForm = {
      type: 'OForm',
      left: lastHalf.left,
      leftUnforms: lastHalf.leftUnforms,
      closedForm: lastHalf.closedForm,
      rightUnforms: lastHalf.rightUnforms,
      right: acc
    };
    return opStateRoll({ completed: s.completed, halfOpen: restHalfs }, newAcc);
  }
}

function opPushForm(
  os: OpState,
  acc: OpenForm | null,
  seAcc: Unforms,
  f: ClosedForm
): OpState {
  if (os.halfOpen.length === 0) {
    if (acc === null) {
      return {
        completed: os.completed,
        halfOpen: [{
          type: 'HOForm',
          left: null,
          leftUnforms: [],
          closedForm: f,
          rightUnforms: []
        }]
      };
    } else if (wantsLeftChild(headOf(f).value)) {
      return {
        completed: os.completed,
        halfOpen: [{
          type: 'HOForm',
          left: acc,
          leftUnforms: seAcc,
          closedForm: f,
          rightUnforms: []
        }]
      };
    } else {
      throw new Error("I'm curious whether this is possible");
    }
  } else {
    const face = os.halfOpen[os.halfOpen.length - 1];
    const restHalfs = os.halfOpen.slice(0, -1);
    
    const comparison = compareTokens(faceOfHalfOpenForm(face).value, headOf(f).value);
    
    switch (comparison.type) {
      case 'Shift':
        return {
          completed: os.completed,
          halfOpen: [...os.halfOpen, {
            type: 'HOForm',
            left: acc,
            leftUnforms: seAcc,
            closedForm: f,
            rightUnforms: []
          }]
        };
        
      case 'Reduce':
        if (acc === null) {
          const accPrime: OpenForm = {
            type: 'OForm',
            left: face.left,
            leftUnforms: face.leftUnforms,
            closedForm: face.closedForm,
            rightUnforms: [],
            right: null
          };
          return opPushForm(
            { completed: os.completed, halfOpen: restHalfs },
            accPrime,
            [...face.rightUnforms, ...seAcc],
            f
          );
        } else {
          const accPrime: OpenForm = {
            type: 'OForm',
            left: face.left,
            leftUnforms: face.leftUnforms,
            closedForm: face.closedForm,
            rightUnforms: face.rightUnforms,
            right: acc
          };
          return opPushForm(
            { completed: os.completed, halfOpen: restHalfs },
            accPrime,
            seAcc,
            f
          );
        }
        
      case 'Roll':
        const seAccPrime = seAcc.map(f => ({ type: 'Unform' as const, unform: f }));
        const completedPrime = [...opStateRoll(os, acc), ...seAccPrime];
        return {
          completed: completedPrime,
          halfOpen: [{
            type: 'HOForm',
            left: null,
            leftUnforms: [],
            closedForm: f,
            rightUnforms: []
          }]
        };
    }
  }
}

function opPush(os: OpState, f: Sharded<ClosedForm>): OpState {
  switch (shardMode) {
    case 'ShardsSecondary':
      switch (f.type) {
        case 'Unform':
          if (os.halfOpen.length === 0) {
            return {
              completed: [...os.completed, { type: 'Unform', unform: f.unform }],
              halfOpen: []
            };
          } else {
            const lastHalf = os.halfOpen[os.halfOpen.length - 1];
            const restHalfs = os.halfOpen.slice(0, -1);
            return {
              completed: os.completed,
              halfOpen: [...restHalfs, {
                ...lastHalf,
                rightUnforms: [...lastHalf.rightUnforms, f.unform]
              }]
            };
          }
        case 'Form':
          return opPushForm(os, null, [], f.form);
      }
      
    case 'ShardsObstructive':
      switch (f.type) {
        case 'Unform':
          if (f.unform.type === 'Secondary') {
            if (os.halfOpen.length === 0) {
              return {
                completed: [...os.completed, { type: 'Unform', unform: f.unform }],
                halfOpen: []
              };
            } else {
              const lastHalf = os.halfOpen[os.halfOpen.length - 1];
              const restHalfs = os.halfOpen.slice(0, -1);
              return {
                completed: os.completed,
                halfOpen: [...restHalfs, {
                  ...lastHalf,
                  rightUnforms: [...lastHalf.rightUnforms, f.unform]
                }]
              };
            }
          } else { // Shard
            return {
              completed: [...opStateRoll(os, null), { type: 'Unform', unform: f.unform }],
              halfOpen: []
            };
          }
        case 'Form':
          return opPushForm(os, null, [], f.form);
      }
  }
}

function closePartialForm(f: PartialForm): ClosedForm {
  switch (f.type) {
    case 'Head':
      return { type: 'Head', token: f.token };
    case 'Match':
      return {
        type: 'Match',
        form: closePartialForm(f.form),
        items: operatorize(f.items),
        token: f.token
      };
  }
}

function closeShardePartialForm(f: Sharded<PartialForm>): Sharded<ClosedForm> {
  switch (f.type) {
    case 'Unform':
      return { type: 'Unform', unform: f.unform };
    case 'Form':
      return { type: 'Form', form: closePartialForm(f.form) };
  }
}

function opPushes(s: OpState, fs: Sharded<PartialForm>[]): OpState {
  let result = s;
  for (const f of fs) {
    result = opPush(result, closeShardePartialForm(f));
  }
  return result;
}

function operatorize(fs: Sharded<PartialForm>[]): Sharded<OpenForm>[] {
  return opStateRoll(opPushes({ completed: [], halfOpen: [] }, fs), null);
}

export function parse(tokens: Ranged<Token>[]): Sharded<OpenForm>[] {
  return operatorize(matchParse(tokens));
}
