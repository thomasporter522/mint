import { LRLanguage, LanguageSupport } from '@codemirror/language'
import { styleTags, tags as t } from '@lezer/highlight'
// @ts-ignore — generated module
import { parser } from './grammar/mint.grammar.js'

const mintParser = parser.configure({
  props: [
    styleTags({
      'Postulate_kw Construct_kw Meta_kw By_kw End_kw Schema_kw Coerce_kw Let_kw In_kw Match_kw With_kw Fun_kw If_kw Then_kw Else_kw': t.keyword,
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

const mintLanguage = LRLanguage.define({
  parser: mintParser,
  languageData: {
    commentTokens: { line: '--' },
    closeBrackets: { brackets: ['(', '['] },
  },
})

export function mint(): LanguageSupport {
  return new LanguageSupport(mintLanguage)
}
