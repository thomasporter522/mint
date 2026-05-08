import { useState, useEffect, useMemo, useRef } from 'react'
import ReactMarkdown from 'react-markdown'
import CodeMirror from '@uiw/react-codemirror'
import { EditorView } from '@codemirror/view'
import { EditorState } from "@codemirror/state";
import { linter, type Diagnostic } from '@codemirror/lint'

import './App.css'

import { mintTheme } from "./CodeTheme"
import { getStaticsFromCode, printTerm } from './frontend/reason-bridge'
import { mint } from './frontend/language'

import type { holeInfo, Term, Error } from './frontend/types'
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
  const [semanticErrors, setSemanticErrors] = useState<Error[]>([])
  const [holes, setHoles] = useState<[Number,holeInfo][]>([])
  const [currentHole, setCurrentHole] = useState<holeInfo | undefined>(undefined)
  const [infoPanelWidth, setInfoPanelWidth] = useState<number>(32)
  const isDragging = useRef(false)

  const setSemanticErrorsRef = useRef(setSemanticErrors)
  setSemanticErrorsRef.current = setSemanticErrors
  const updateHolesRef = useRef<(h: [Number, holeInfo][]) => void>(() => {})

  const mintLinter = useMemo(() =>
    linter((view) => {
      const code = view.state.doc.toString()
      const statics = getStaticsFromCode(code)
      setSemanticErrorsRef.current(statics.errors)
      updateHolesRef.current(statics.holes)
      return statics.errors
        .filter((e: Error) => e.from >= 0 && e.from < e.to)
        .map((e: Error): Diagnostic => ({
          from: e.from,
          to: e.to,
          severity: "error",
          message: e.message,
        }))
    }, { delay: 0 }),
  [])
  
  // const urlParams = new URLSearchParams(window.location.search)
  // const itemId = urlParams.get('item')
  // const courseIds = urlParams.get('course')

  const itemId = "item"
  const courseIds = "contents"
   
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

  const replacements = [["\\->", "⟼"]]

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

  // Drag-to-resize info panel
  const handleMouseDown = () => {
    isDragging.current = true
    document.body.style.cursor = 'col-resize'
    document.body.style.userSelect = 'none'
  }

  useEffect(() => {
    const handleMouseMove = (e: MouseEvent) => {
      if (!isDragging.current) return
      const windowWidth = window.innerWidth
      const newWidth = ((windowWidth - e.clientX) / windowWidth) * 100
      setInfoPanelWidth(Math.max(10, Math.min(60, newWidth)))
    }
    const handleMouseUp = () => {
      isDragging.current = false
      document.body.style.cursor = ''
      document.body.style.userSelect = ''
    }
    document.addEventListener('mousemove', handleMouseMove)
    document.addEventListener('mouseup', handleMouseUp)
    return () => {
      document.removeEventListener('mousemove', handleMouseMove)
      document.removeEventListener('mouseup', handleMouseUp)
    }
  }, [])

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

  function updateHoles(newHoles : [Number, holeInfo][]) {
    setHoles(newHoles)
    const newCurrentHole = lookup(newHoles,cursorPosition) || lookup(newHoles, cursorPosition - 1);
    setCurrentHole(newCurrentHole)
  }
  updateHolesRef.current = updateHoles;

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
            '.cm-scroller': {
              overflowY: 'hidden',
              overflowX: 'auto',
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
                  <DisplayCodeBlock code={printTerm(entry[1])} />
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
          {semanticErrors.map((error: Error, i: number) => (
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
    let contents = <></>;
    if(holes.length + semanticErrors.length === 0) {
      contents = 
        <div className='victory-sidebar'></div>
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
    return <div className='item-info-sidebar' style={{ width: `${infoPanelWidth}%` }}>
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
            {/* <div className='item-contents-sidebar'>
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
            </div> */}
            <div className='item-middle'>
              <div className='item-text'>
                <ReactMarkdown>{page.data.text}</ReactMarkdown>
              </div>
              <div className='item-form'>
                {/* <code><ReactMarkdown>{page.data.type}</ReactMarkdown></code> */}

                <CodeMirror
                  value={page.data.type}
                  height="100%"
                  theme={mintTheme}
                  extensions={[
                    mint(),
                    EditorView.theme({
                      '.cm-editor': {
                        width: '100%',
                      },
                      '.cm-scroller': {
                        overflow: 'auto'
                      },
                      '.cm-content': {
                        whiteSpace: 'pre'  // Prevent text wrapping
                      },
                      '.cm-line': {
                        whiteSpace: 'pre'  // Prevent line wrapping
                      }
                    }),
                    mintLinter,
                    autoReplace,
                  ]}
                  basicSetup={{
                    history: true,
                    foldGutter: false,
                    dropCursor: false,
                    allowMultipleSelections: false,
                    bracketMatching: true,
                  }}
                  onUpdate={(viewUpdate) => {
                    const cursor = viewUpdate.state.selection.main.head
                    setCursorPosition(cursor)
                    setCurrentHole(lookup(holes,cursor) || lookup(holes, cursor - 1))
                  }}
                />
              </div>
            </div>
            <div className='resize-handle' onMouseDown={handleMouseDown} />
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