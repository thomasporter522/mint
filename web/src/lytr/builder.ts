import type { Ranged } from './utils';
import type { PrimaryToken } from './grammar';
import type { Sharded, OpenForm, ClosedForm, Unforms , Unform} from './parser';
import type { Term } from './term';
import { meta } from './term';

function combineTerms(ts : Term[]) : Term {
  if(ts.length === 0) {
    return meta({type:"Hole", inserted:true})
  } else if (ts.length === 1) {
    return ts[0]
  }
  return meta({type : "Ap", fun:ts[0], args:ts.slice(1)})
}

function buildTerms(fs: Sharded<OpenForm>[]): Term {
  const ts = fs.map(buildSharded).flat();
  return combineTerms(ts)
}

function buildLeftChild(form: OpenForm | null, unforms: Unforms): Term {
  const ts = form ? [buildForm(form),...buildUnforms(unforms)] : buildUnforms(unforms)
  return combineTerms(ts)
}

function buildRightChild(unforms: Unforms, form: OpenForm | null): Term {
  const ts = form ? [...buildUnforms(unforms),buildForm(form)] : buildUnforms(unforms)
  return combineTerms(ts)
}

// function buildCaseBranches(form: ClosedForm, is: Sharded<OpenForm>[]): [Term, [Term, Term][]] {
//   switch (form.type) {
//     case 'Head':
//       if (form.token.value.type === 'TCase') {
//         return [buildTerms(is), []];
//       }
//       throw new Error('impossible; ill structured case form');
      
//     case 'Match':
//       if (form.form.type === 'Match' && 
//           form.form.token.value.type === 'TPipe' && 
//           form.token.value.type === 'TDoubleArrow') {
//         const [scrutinee, cases] = buildCaseBranches(form.form.form, form.form.items);
//         return [scrutinee, [...cases, [buildTerms(form.items), buildTerms(is)]]];
//       }
//       throw new Error('impossible; ill structured case form');
//   }
// }


    // if(closedForm.form.type === 'Head' && closedForm.form.token.value.type === 'TEnd') {
    //   console.log("baba")
    //   return meta({ type: 'Postulate', body : [], rest: null});
    // } 
    // console.log("booie")
    // const restForm : OpenForm = {type:"OForm", left:null, leftUnforms:[], closedForm:closedForm.form, rightUnforms, right};
    // return meta({ type: 'Postulate', body : [], rest: buildForm(restForm)});

function buildItem(item : Sharded<OpenForm>) : Term | null {
  if (item.type === "Unform") {
    return null
  } 
  return buildForm(item.form)
}

function buildItems(items : Sharded<OpenForm>[]) : Term[] {
  return items.map(buildItem).filter(x => x !== null)
}

function buildBlocks(form : ClosedForm, contents : Sharded<OpenForm>[], rest : Term | null) : Term {
  if(form.token.value.type === "TPostulate") {
    const body = buildItems(contents)
    if(form.type === "Head") {
      return meta({type:"Postulate", body, rest})
    }
    return buildBlocks(form.form, form.items, meta({type:"Postulate", body, rest}))
  }
  return meta({type: "BUILDER ERROR"});
}

function localize(term : Term, token: Ranged<PrimaryToken>) : Term {
  return {...term, meta:{...term.meta, start:token.start, end:token.end}}
}

/* Precondition: the input begins, ends, and matches validly */
function buildForm(form: OpenForm): Term {

  const { left, leftUnforms, closedForm, rightUnforms, right } = form;

  const isEmptyUnforms = (unforms: Unforms) => unforms.length === 0;

  // parens
  if (left === null && isEmptyUnforms(leftUnforms) && 
      closedForm.type === 'Match' && 
      closedForm.token.value.type === 'TCP' && 
      closedForm.form.type === 'Head' && 
      closedForm.form.token.value.type === 'TOP' && 
      isEmptyUnforms(rightUnforms) && right === null) {
    const term = buildTerms(closedForm.items);
    return {...term, meta:{...term.meta, parens:true}};
  }

  // Atoms
  if (left === null && isEmptyUnforms(leftUnforms) && 
      closedForm.type === 'Head' && 
      closedForm.token.value.type === 'TAtom' && 
      isEmptyUnforms(rightUnforms) && right === null) {
    const atom = closedForm.token.value.atom
    switch (atom.type) {
      case "Hole": {
        var t = meta({type: "Hole", inserted:false});
        return localize(t, closedForm.token)
      }
      case "Identifier": {
        var t = meta({type: "Identifier", value:atom.value})
        return localize(t, closedForm.token)
      }
    }
  }

  // Binary operations
  if (closedForm.type === 'Head' && closedForm.token.value.type === 'TColon') {
    var t = meta({
      type: 'Asc',
      left: buildLeftChild(left, leftUnforms),
      right: buildRightChild(rightUnforms, right)
    });
    return localize(t, closedForm.token)
  }

  if (right === null && isEmptyUnforms(rightUnforms) && 
      closedForm.type === 'Match' && 
      closedForm.token.value.type === 'TEnd') {
    return buildBlocks(closedForm.form, closedForm.items, null)
  }

  console.log("incoming")

  console.log("BUILDER ERROR: ", form)
  return meta({type: "BUILDER ERROR"});
}

function buildUnform(unform: Unform): Term[] {
    if (unform.type === "Secondary"){ return [] }
    return [meta({ type: 'Shard', token: unform.token.value })];
}

function buildUnforms(unforms: Unforms): Term[] {
    return unforms.map(buildUnform).flat()
}

function buildSharded(sof: Sharded<OpenForm>): Term[] {
  switch (sof.type) {
    case 'Unform':
      return buildUnform(sof.unform)
    case 'Form':
      return [buildForm(sof.form)];
  }
}

export function build(forms: Sharded<OpenForm>[]): Term {
  return buildTerms(forms)
}