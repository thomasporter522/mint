export interface Ranged<A> {
  value: A;
  start: number;
  end: number;
}

export function mapRanged<A,B>(f : Function, a : Ranged<A>) : Ranged<B> {
  return {value : f(a.value), start:a.start, end:a.end}
}