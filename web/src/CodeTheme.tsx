import { EditorView } from '@codemirror/view'
import { HighlightStyle, syntaxHighlighting } from '@codemirror/language'
import { tags as t } from '@lezer/highlight'

const mintHighlightStyle = HighlightStyle.define([
  { tag: t.operator, color: 'var(--operator-color)'},
  { tag: t.variableName, color: 'var(--variable-color)' },
  { tag: t.keyword, color: 'var(--keyword-color)' },
  { tag: t.paren, color: 'var(--mint-color)' },
  { tag: t.separator, color: 'var(--mint-color)' },
  { tag: t.punctuation, color: 'var(--hole-color)' },
  { tag: t.invalid, color: 'var(--invalid-parse-color)' },
  // { tag: t.string, color: 'var(--mint-color)' },
  // { tag: t.comment, color: 'var(--mint-color)' },
  // { tag: t.lineComment, color: 'var(--mint-color)'},
  // { tag: t.number, color: 'var(--mint-color)'},
  // { tag: t.function(t.variableName), color: 'var(--mint-color)' }
])

const mintEditorTheme = EditorView.theme({
  '&': {
    color: 'var(--mint-color)',
    backgroundColor: 'var(--background-color)',
    fontSize: '15pt'
  },
  '& *': {
    fontFamily: "'FiraCode' !important"
  },
  '.cm-content': {
    padding: '16px',
    minHeight: '200px'
  },
  '.cm-focused': {
    outline: 'none'
  },
  '.cm-editor': {
    borderRadius: '0px',
  },
  '.cm-line': {
    padding: '0 2px',
    lineHeight: '1.6'
  },
  '.cm-cursor': {
    borderLeft: '2px solid var(--mint-color)'
  },
  '.cm-selectionBackground': {
    backgroundColor: 'var(--mint-color-hover) !important',
    opacity: '0.3',
  },
  '.cm-activeLine': {
    backgroundColor: 'transparent' ,
  },
  // gutters
  '.cm-gutters': {
    backgroundColor: 'var(--background-color)', // Background of the gutter area
    color: 'var(--mint-color)', // Line number text color
    border: 'none',
    borderRight: '2px solid var(--dark-border-color)'
  },
  '.cm-activeLineGutter': {
    backgroundColor: 'inherit', // Active line number background
    color: 'inherit' // Active line number text color
  },
}, { dark: true })

export const mintTheme = [
  mintEditorTheme,
  syntaxHighlighting(mintHighlightStyle)
]