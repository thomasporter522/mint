type ranged('a) = {
  value: 'a,
  start: int,
  end_: int,
};

let mapRanged = (f, r) => {value: f(r.value), start: r.start, end_: r.end_};

let noRange = v => {value: v, start: (-1), end_: (-1)};
