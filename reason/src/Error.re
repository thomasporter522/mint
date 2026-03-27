type error = {
  type_: string,
  message: string,
  from: int,
  to_: int,
};

let mark = (message, from, to_) => {type_: "mark", message, from, to_};
