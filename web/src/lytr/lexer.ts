import type { Ranged } from './utils';
import type { Token, PrimaryToken } from './grammar';

// Helper function to check if a character is whitespace
function isWhitespace(c: string): boolean {
  return c === ' ' || c === '\t' || c === '\n' || c === '\r';
}

// Helper function to check if a character is a digit
function isDigit(c: string): boolean {
  return c >= '0' && c <= '9';
}

// Helper function to check if a character is a letter
function isLetter(c: string): boolean {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

// Helper function to check if a character is alphanumeric
function isAlphanum(c: string): boolean {
  return isLetter(c) || isDigit(c) || c === '_' || c === '-';
}

// Main lexer function
export function lex(s: string): Ranged<Token>[] {
  const tokens: Ranged<Token>[] = [];
  let i = 0;

  while (i < s.length) {
    const start = i;
    const char = s[i];

    // Whitespace
    if (isWhitespace(char)) {
      tokens.push({
        value: { type: 'Secondary', token: { type: 'Whitespace', value: char } },
        start,
        end: i + 1
      });
      i++;
      continue;
    }


    // Letters (identifiers and keywords)
    if (isLetter(char)) {
      let j = i;
      while (j < s.length && isAlphanum(s[j])) {
        j++;
      }
      const idStr = s.substring(i, j);

      // Check if it's a keyword
      let primaryToken: PrimaryToken;
      switch (idStr) {
        case 'postulate': primaryToken = { type: 'TPostulate' }; break;
        case 'checker': primaryToken = { type: 'TChecker' }; break;
        case 'construct': primaryToken = { type: 'TConstruct' }; break;
        case 'end': primaryToken = { type: 'TEnd' }; break;
        default: primaryToken = { type: 'TAtom', atom: { type: 'Identifier', value: idStr } };
      }

      tokens.push({
        value: { type: 'Primary', token: primaryToken },
        start: i,
        end: j
      });
      i = j;
      continue;
    }

    // Single-character tokens
    let singleCharToken: Token | null = null;

    switch (char) {
      case '(': singleCharToken = { type: 'Primary', token: { type: 'TOP' } }; break;
      case ')': singleCharToken = { type: 'Primary', token: { type: 'TCP' } }; break;
      case '?': singleCharToken = { type: 'Primary', token: { type: 'TAtom', atom: { type: 'Hole' } } }; break;
      case ':': singleCharToken = { type: 'Primary', token: { type: 'TColon' } }; break;
    }

    if (singleCharToken) {
      tokens.push({
        value: singleCharToken,
        start,
        end: i + 1
      });
      i++;
      continue;
    }

    // Unknown character - treat as unlexed
    tokens.push({
      value: { type: 'Secondary', token: { type: 'Unlexed', value: char } },
      start,
      end: i + 1
    });
    i++;
  }

  return tokens;
}