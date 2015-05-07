open Core.Std

module F = Format
module L = List

let optional ~d v = Option.value ~default:d v
