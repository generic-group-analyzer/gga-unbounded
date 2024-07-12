open Core

module F = Format
module L = List

let optional ~d v = Option.value ~default:d v

let fixme s = failwith ("FIXME: "^s)
