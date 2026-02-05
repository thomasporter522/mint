import { useState, useEffect } from 'react'
import ReactMarkdown from 'react-markdown'
import CodeMirror from '@uiw/react-codemirror'
import { EditorView, Decoration } from '@codemirror/view'
import { EditorState } from "@codemirror/state";

import './App.css'

import { mintTheme } from "./CodeTheme"
import { lex } from './lytr/lexer'
import { parse } from './lytr/parser'
import { printTerm } from './lytr/print'
import { build } from './lytr/builder'
// import { mintlang } from './CodeLanguage'

import { getStatics } from './semantics/Check'
import type { holeInfo } from './semantics/Check'
import type { Term } from './lytr/term'
import type { Error } from './semantics/Error'
// import {prettyProposition} from './semantics/Pretty'


interface Item {
  title: string
  text: string
  type: string
  tags: string[]
}

interface Course {
  title: string
  description: string
  sequence: string[]
}

type CourseEntry =
  | { type: 'item', data: Item }
  | { type: 'course', data: Course }

type PageState = 
  | { type: 'loading' }
  | { type: 'item', data: Item, course: Course, entries: CourseEntry[], atlas: any}
  | { type: 'error', message: string }

function lookup<A,B>(l : [A,B][], x : A) : B | undefined {
  const y = l.find(e => e[0] === x);
  return y ? y[1] : undefined
}

function App() {
  const [page, setPage] = useState<PageState>({ type: 'loading' })
  const [cursorPosition, setCursorPosition] = useState<number>(0)
  const [semanticErrors, setSemanticErrors] = useState<any[]>([])
  const [holes, setHoles] = useState<[Number,holeInfo][]>([])
  const [currentHole, setCurrentHole] = useState<holeInfo | undefined>(undefined)
  
  const urlParams = new URLSearchParams(window.location.search)
  const itemId = urlParams.get('item')
  const courseIds = urlParams.get('course')
   
  useEffect(() => {
    async function loadPage() {
      try {
        if (itemId) {
          const [itemRes, courseRes, atlasRes] = await Promise.all([
            fetch('/content/items.json'),
            fetch('/content/courses.json'),
            fetch('/content/atlas.json')
          ])
          const items = await itemRes.json()
          const courses = await courseRes.json()
          const atlas = await atlasRes.json()
          
          if (items[itemId]) {
            // If we also have course context, load that too
            if (courseIds) {
              const courseIdList = courseIds.split(",")
              const courseId = courseIdList[courseIdList.length-1]
              
              if (courses[courseId]) {
                const courseData = courses[courseId]
                const courseEntries = courseData.sequence.map((id: string) => {
                  if (items[id]) {
                    return { type: 'item' as const, data: items[id] }
                  } else if (courses[id]) {
                    return { type: 'course' as const, data: courses[id] }
                  }
                  return null
                }).filter((entry: CourseEntry): entry is CourseEntry => entry !== null)
                
                setPage({ type: 'item', data: items[itemId], course: courseData, entries: courseEntries, atlas })
              } else {
                setPage({ type: 'item', data: items[itemId], course: { title: '', description: '', sequence: [] }, entries: [], atlas })
              }
            } else {
              setPage({ type: 'item', data: items[itemId], course: { title: '', description: '', sequence: [] }, entries: [], atlas })
            }
          } else {
            setPage({ type: 'error', message: 'Item not found' })
          }
        }
      } catch (error) {
        setPage({ type: 'error', message: 'Failed to load data' })
      }
    }
    
    loadPage()
  }, [itemId, courseIds])

  const replacements = [["\\->", "⟼"], ["happy", "😊"]]//, ["<", "◁"]]

  const autoReplace = EditorState.transactionFilter.of(tr => {
    if (!tr.isUserEvent("input")) return tr;

    let changes: any[] = [];

    tr.changes.iterChanges((_fromA, _toA, fromB, _toB, inserted) => {
      const doc = tr.newDoc;
      const lookBehind = 10;
      const start = Math.max(0, fromB - lookBehind);
      const context = doc.sliceString(start, fromB);

      for (const [before, after] of replacements) {
        const idx = context.lastIndexOf(before.slice(0, before.length-1));
        if (idx !== -1 && (idx + before.length - 1) === context.length && inserted.toString() === before.slice(before.length -1, before.length)) {
          const from = start + idx;  // replace the last two chars "-->"
          const to = start + idx + (before.length - 1);
          changes.push({ from, to, insert: after });
        }
      }
    });

    return changes.length ? [{ changes }] : tr;
  });

  function urlOfEntry(entry: CourseEntry, entry_id: string) {
    let newUrl = window.location.pathname

    if (entry.type === 'item') {
      const newParams = new URLSearchParams(window.location.search)
      newParams.set('item', entry_id)
      newUrl += '?' + newParams.toString()
    } else if (entry.type === 'course') {
      const currentCourse = new URLSearchParams(window.location.search).get('course') || ''
      newUrl += `?course=${currentCourse}%2C${entry_id}`
    }
    return newUrl
  }

  function urlWithoutItem() {
    let newUrl = window.location.pathname
    const newParams = new URLSearchParams(window.location.search)
    newParams.delete('item')
    newUrl += '?' + newParams.toString()
    return newUrl
  }

  function updateHoles(holes : [Number, holeInfo][]) {
    setHoles(holes)
    const newCurrentHole = lookup(holes,cursorPosition) || lookup(holes, cursorPosition - 1);
    setCurrentHole(newCurrentHole)
  }

  function DisplayCodeBlock({ code, height = "auto" }: { code: string, height?: string }) {
    const lineCount = code.split('\n').length + 1
    const calculatedHeight = `${(lineCount) * 20}px` // 20px per line + 1 extra line
    
    return (
      <CodeMirror
        value={code}
        height={height === "auto" ? calculatedHeight : height}
        theme={mintTheme}
        extensions={[
          EditorView.theme({
            '.cm-content': {
              padding: '3px !important',
              margin: '0px !important',
              minHeight: '0px !important'
            },
          })
        ]}
        basicSetup={{
          lineNumbers: false,
          foldGutter: false,
          dropCursor: false,
          allowMultipleSelections: false,
          searchKeymap: false,
          autocompletion: false,
          closeBrackets: false,
          history: false
        }}
        editable={false}
      />
    )
  }

  function displayCurrentHole(h : holeInfo | undefined) {    
    if(h) {
      const goal = <>Goal: <DisplayCodeBlock code={printTerm(h.goal)} /></>
      const context = <>Context: {[...h.context.entries()].map((entry: [string, Term], i: number) => (
              <div key={i}>
                <div className="context-entry" style={{ padding: '0px 0px 3px 0px'}}>
                  {/* {entry[0]} : {prettyProposition(entry[1])} */}
                  {/* {entry[0]} : <DisplayCodeBlock code={prettyProposition(entry[1])} /> */}
                  <DisplayCodeBlock code={entry[0] + " : " + printTerm(entry[1])} /> 
                </div>
              </div>
            ))}</>
      if(h.context.size > 0) {
        return <div className='item-inspector-sidebar'>
          {goal}
          {context}
        </div>
      } else {
        return <div className='item-inspector-sidebar'>
          {goal}
        </div>
      }
    } else {
      return <></>
    }
  }

  function messageOfError(error : Error) {
    const position = error.from == error.to ? "" + error.from : error.from + "-" + error.to
    return error.to >= 0 ? "[" + position + "] " + error.message : error.message
  }

  function messageOfGoal(hole : [Number, holeInfo]) {
    // return "[" + goal[0] + "] " + prettyProposition(goal[1])
    return <DisplayCodeBlock code={printTerm(hole[1].goal)}/>
  }

  function goalsDisplay() {
    const otherHoles = holes
          .filter(goal => goal[0] !== cursorPosition && goal[0] !== cursorPosition-1);
    if(otherHoles.length == 0) {
      return <></>
    }
    const suffix = otherHoles.length > 1 ? "s" : "";
    return <div>
      <span>
        {(currentHole ? "Other goal" : "Goal") + suffix + ":"}
      </span>
        <div>
          {otherHoles.map((hole: [Number, holeInfo], i: number) => (
            <div key={i}>
              <div className="goal-message" style={{ padding: '0px 0px 3px 0px'}}>
                {messageOfGoal(hole)}
              </div>
            </div>
          ))}
        </div>
    </div>
  }

  function errorsDisplay() {
    if(semanticErrors.length == 0) {
      return <></>
    }
    return <div>
        <span style={{ color: 'var(--error-text-color)'}}>
          Errors:
        </span>
        <div>
          {semanticErrors.map((error: any, i: number) => (
            <div key={i}>
              <div className="error-message">
                {messageOfError(error)}
              </div>
            </div>
          ))}
        </div>
    </div>
  }

  function infoDisplay() {
    var contents = <></>;
    if(holes.length + semanticErrors.length === 0) {
      contents = 
        <div className='victory-sidebar'>
          Solved!
        </div>
    }
    else {
      contents = <div>
          {displayCurrentHole(currentHole)}
          <div className='item-agenda-sidebar'>
            <div>
              {goalsDisplay()}
              {errorsDisplay()}
            </div>
        </div>
      </div>
    }
    return <div className='item-info-sidebar'>
        {contents}
      </div>
  }

  switch (page.type) {
    case 'loading':
      return <div>Loading...</div>

    case 'item':
      return (
        <div className="page-with-topbar">
          <div className="topbar">
            <span className="item-title">
              <ReactMarkdown>{page.data.title}</ReactMarkdown>
            </span>
          </div>
          <div className='item'>
            <div className='item-contents-sidebar'>
              <div><a href={urlWithoutItem()}><ReactMarkdown>{page.course.title}</ReactMarkdown></a></div>
              <div className='item-contents-sidebar-contents'>
                <ol>
                  {page.entries.map((entry, index) => {
                    const sequenceId = page.course.sequence[index]
                    const current = entry.data == page.data;
                    const classname = current ? "current-entry" : "";
                    return (
                    <li key={index} className="course-entry">
                      <a href={urlOfEntry(entry, sequenceId)}>
                        <p className={classname}>{entry.data.title}</p>
                      </a>
                    </li>
                  )
                  })}
                </ol>
              </div>
            </div>
            <div className='item-middle'>
              <div className='item-text'>
                <ReactMarkdown>{page.data.text}</ReactMarkdown>
              </div>
              <div className='item-form'>
                {/* <code><ReactMarkdown>{page.data.type}</ReactMarkdown></code> */}

                <CodeMirror
                  value={page.data.type}
                  height="400px"
                  theme={mintTheme}
                  extensions={[
                    // mintlang(),
                    EditorView.theme({
                      '.cm-editor': {
                        // width: '100%',
                        width: '600px',
                        maxWidth: '600px'
                      },
                      '.cm-scroller': {
                        overflow: 'false'  // Enable horizontal scrolling
                      },
                      '.cm-content': {
                        whiteSpace: 'pre'  // Prevent text wrapping
                      },
                      '.cm-line': {
                        whiteSpace: 'pre'  // Prevent line wrapping
                      }
                    }),
                    EditorView.decorations.of(Decoration.set(
                      semanticErrors
                        .filter(error => (error.type !== "hole"))
                        .filter(error => (error.from < error.to))
                        .sort((a, b) => a.from - b.from)
                        .map(error => 
                          Decoration.mark({
                            class: "semantic-error"
                          }).range(error.from, error.to)
                        )
                    )),
                    EditorView.decorations.of(Decoration.set(
                      holes
                        .sort((a, b) => (a[0].valueOf() - b[0].valueOf()))
                        .map(h => 
                          Decoration.mark({
                            class: "hole"
                          }).range(h[0].valueOf(), h[0].valueOf()+1)
                        )
                    )),
                    autoReplace,
                  ]}
                  basicSetup={{
                    history: true,
                    foldGutter: false,
                    dropCursor: false,
                    allowMultipleSelections: false,
                  }}
                  onChange={(val, viewUpdate) => {
                    // Check semantic errors when code changes
                    // console.log(printTerm(build(parse(lex(val)))))
                    if (viewUpdate?.view) {
                      const statics = getStatics(build(parse(lex(val))))
                      setSemanticErrors(statics.errors)
                      updateHoles(statics.holes)
                    }
                  }}
                  onCreateEditor={(view) => {
                    // Check errors when editor is first created
                    setTimeout(() => {
                      // console.log(build(parse(lex(view.state.doc.toString()))))
                      const statics = getStatics(build(parse(lex(view.state.doc.toString()))))
                      setSemanticErrors(statics.errors)
                      updateHoles(statics.holes)
                    }, 100)
                  }}
                  onUpdate={(viewUpdate) => {
                    const cursor = viewUpdate.state.selection.main.head
                    setCursorPosition(cursor)
                    setCurrentHole(lookup(holes,cursor) || lookup(holes, cursor - 1))
                  }}
                />
              </div>
            </div>
            {infoDisplay()}
          </div>
        </div>
      )

    case 'error':
      return <div>Error: {page.message}</div>

    default:
      return <div>Unknown state</div>
  }
}

export default App