(*
   LinIR backend for the Austral compiler.
*)
open Env
open Stages.Mtast

(** Generate LinIR code for a monomorphized module. *)
val gen_lir_module : env -> mono_module -> string
