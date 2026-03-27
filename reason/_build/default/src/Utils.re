type ranged('a) = {
  value: 'a,
  start: int,
  end_: int,
};

let mapRanged = (f, a) => {value: f(a.value), start: a.start, end_: a.end_};
