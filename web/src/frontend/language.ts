import { LRLanguage, LanguageSupport } from '@codemirror/language'
import { styleTags, tags as t } from '@lezer/highlight'
// @ts-ignore — generated module
import { parser } from './grammar/lytr.grammar.js'

const lytrParser = parser.configure({
  props: [
    styleTags({
      'Postulate_kw Construct_kw Meta_kw By_kw End_kw Schema_kw Let_kw In_kw Match_kw With_kw Fun_kw If_kw Then_kw Else_kw': t.keyword,
      Identifier: t.variableName,
      Hole: t.punctuation,
      StringLit: t.string,
      LineComment: t.lineComment,
      LParen: t.paren,
      RParen: t.paren,
      LBracket: t.squareBracket,
      RBracket: t.squareBracket,
      'Wildcard ":" "=" "|" "->" "=>" "==" "!=" "&&" "||" "::"': t.operator,
    }),
  ],
})

const lytrLanguage = LRLanguage.define({
  parser: lytrParser,
  languageData: {
    commentTokens: { line: '--' },
    closeBrackets: { brackets: ['(', '['] },
  },
})

export function lytr(): LanguageSupport {
  return new LanguageSupport(lytrLanguage)
}
