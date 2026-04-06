import { NodeProp, NodeSet, NodeType, Parser, Tree } from '@lezer/common'
import type { TreeFragment, Input, PartialParse } from '@lezer/common'
import { styleTags, tags as t } from '@lezer/highlight'
import { Language, defineLanguageFacet } from '@codemirror/language'
// @ts-ignore
import { lexToTokens } from '@reason/Lytr_api.js'

/* ------------------------------------------------------------------ */
/*  Node types (IDs must match Lytr_api.re lexToTokens)                */
/* ------------------------------------------------------------------ */

const nodeTypes = [
  /* 0 */ NodeType.define({ id: 0, name: "Document", top: true }),
  /* 1 */ NodeType.define({ id: 1, name: "Keyword" }),
  /* 2 */ NodeType.define({ id: 2, name: "Identifier" }),
  /* 3 */ NodeType.define({ id: 3, name: "Hole" }),
  /* 4 */ NodeType.define({ id: 4, name: "Colon" }),
  /* 5 */ NodeType.define({ id: 5, name: "OpenParen", props: [[NodeProp.closedBy, ["CloseParen"]]] }),
  /* 6 */ NodeType.define({ id: 6, name: "CloseParen", props: [[NodeProp.openedBy, ["OpenParen"]]] }),
  /* 7 */ NodeType.define({ id: 7, name: "Invalid" }),
]

const nodeSet = new NodeSet(nodeTypes).extend(
  styleTags({
    Keyword: t.keyword,
    Identifier: t.variableName,
    Hole: t.punctuation,
    Colon: t.separator,
    OpenParen: t.paren,
    CloseParen: t.paren,
    Invalid: t.invalid,
  })
)

/* ------------------------------------------------------------------ */
/*  Parser implementation                                              */
/* ------------------------------------------------------------------ */

class LytrParser extends Parser {
  createParse(
    input: Input,
    _fragments: readonly TreeFragment[],
    _ranges: readonly { from: number; to: number }[]
  ): PartialParse {
    const code = input.read(0, input.length)
    const length = input.length

    return {
      parsedPos: length,
      stopAt(_pos: number) {},
      stoppedAt: null,
      advance(): Tree | null {
        const buf = lexToTokens(code) as number[]
        const children: Tree[] = []
        const positions: number[] = []

        for (let i = 0; i < buf.length; i += 3) {
          const type = buf[i]
          const from = buf[i + 1]
          const to = buf[i + 2]
          children.push(new Tree(nodeSet.types[type], [], [], to - from))
          positions.push(from)
        }

        return new Tree(nodeSet.types[0], children, positions, length)
      }
    }
  }
}

/* ------------------------------------------------------------------ */
/*  Language definition                                                 */
/* ------------------------------------------------------------------ */

const lytrParser = new LytrParser()

const lytrLanguage = new Language(
  defineLanguageFacet(),
  lytrParser,
  [],
  "lytr"
)

export function lytr() {
  return lytrLanguage.extension
}
