fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")

(*
 * Fundamentals
 * ============
 * claim    links an identifier and a type
 * alias    links an identifier and a value
 * prim     creates a new primitive value (also for pattern matching)
 * sum      creates a new sum type
 * prod     creates a new prod type
 * lambda   creates a new function
 * ->       create a new function type
 * =        equality ("unwrap" all the definitions)
 * :        bind a name at the type level to a parameter (with usage)
 * macro    introduces a type-less s-expr transformer
 * match    deconstruct a value
 *)

structure Source = struct
  type t = {
    buf: string,
    pos: int ref,
    marks: (string * int) list ref
  }

  fun eof (buf: t): bool =
    (String.size (#buf buf) <= 0) orelse (String.size (#buf buf) <= !(#pos buf))
  fun pos (buf: t): int = !(#pos buf)
  fun peek (buf: t): char = String.sub (#buf buf, !(#pos buf))
  fun try_peek (buf: t): char option =
    if eof buf then NONE else SOME (peek buf)
  fun advance (buf: t): t = ((#pos buf) := !(#pos buf) + 1; buf)
  fun substring (buf: t, i: int, j: int) = String.substring (#buf buf, i, j)


  fun start (buf: t, msg: string): unit =
    (#marks buf) := (msg, !(#pos buf)) :: !(#marks buf)
  fun success (buf: t): unit =
    let val marks = #marks buf
    in marks := (case !marks of
        [] => []
      | (m::ms) => ms)
    end

  fun fromString (str: string): t =
    { buf = str, pos = ref 0, marks = ref [] }
  fun fromStream (ss: TextIO.instream): t =
    let val str = TextIO.inputAll ss
    in fromString str
    end
end

structure Type :> sig
  type t
end = struct
  datatype t =
    FUN of (t vector) * t
  | SUM of t vector
  | PROD of t vector
end

structure Value :> sig
  type t
end = struct
  datatype t =
    LAM of unit
  | PRIM of int
end

structure Ident :> sig
  type t
end = struct
  type t = {
    name: string,
    qtype: Type.t,
    value: Value.t
  }
end

structure Reader : sig
  datatype t =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector

  val read: Source.t -> t option
  val pp: t -> string
end = struct
  (* TODO: figure out how to only have one definition *)
  (* TODO: Annotate each item with its source position, for error handling *)
  datatype t =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector

  (* TODO: some chars can be after the initial pos but not in *)
  fun isAtomChar (c: char): bool =
    let
      fun oneOf str =
        let fun helper i =
          if i >= String.size str then false
          else if String.sub (str, i) = c then true
          else helper (i + 1)
        in helper 0
        end
    in
      ((c >= #"A") andalso (c <= #"Z")) orelse
      ((c >= #"a") andalso (c <= #"z")) orelse
      ((c >= #"0") andalso (c <= #"9")) orelse
      oneOf "!@#$%^&*_+,./<>?;:~"
    end

  fun isWhitespace (c: char): bool =
    case c of
      #" " => true
    | #"\n" => true
    | #"\t" => true
    | _ => false

  fun pp (e: t): string =
    case e of
      ATOM s => s
    | LIST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else " ") ^ (pp e))
      in "(" ^ ((fn (_, x) => x) (Vector.foldl f (true, "") l)) ^ ")"
      end
    | FOREST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else "\n") ^ (pp e))
      in (fn (_, x) => x) (Vector.foldl f (true, "") l)
      end

  local
    fun readAtom (buf: Source.t): t =
      let
        val start = Source.pos buf
        fun helper n =
          case Source.try_peek buf of
            NONE => ATOM (Source.substring (buf, start, n))
          | SOME c =>
            if isAtomChar c
            then (Source.advance buf; helper (n + 1))
            else ATOM (Source.substring (buf, start, n))
      in helper 0
      end

    and readList (buf: Source.t): t option =
      let
        fun helper res =
          case Source.try_peek buf of
            NONE => NONE
          | SOME #")" =>
            (Source.advance buf; SOME (LIST (Vector.fromList (List.rev res))))
          | _ => case readHelper buf of
              NONE => NONE
            | SOME e => helper (e :: res)
      in (Source.advance buf; helper [])
      end

    and readForest (res: t list) (buf: Source.t): t option =
      case readHelper buf of
        NONE => if Source.eof buf
          then SOME (FOREST (Vector.fromList (List.rev res)))
          else NONE
      | SOME e => readForest (e :: res) buf

    and readHelper (buf: Source.t): t option =
      if Source.eof buf then NONE else
      case Source.peek buf of
        #"(" => readList buf
      | c =>
        if isWhitespace c then (readHelper (Source.advance buf))
        else if isAtomChar c then SOME (readAtom buf)
        else NONE
  in
    val read = readForest []
  end
end

structure Parser :> sig
  type t

  val pp: t -> string
  val parse: Reader.t -> t option
end = struct
  datatype t =
    PRIMOP of primop
  | ATOM of string
  | LIST of t vector
  | FOREST of t vector

  and primop =
    CLAIM of string * t
  | ALIAS of string * t
  | LAMBDA
  | FUNCTION
  | BIND
  | SUM
  | PROD
  | MATCH
  | EQUAL
  | PRIM

  fun pp (p: t): string =
    case p of
      PRIMOP p' => (
        case p' of
          CLAIM (s, t) => "(claim " ^ s ^ " " ^ (pp t) ^ ")"
        | ALIAS (s, t) => "(alias " ^ s ^ " " ^ (pp t) ^ ")"
        | _ => "unimplemented"
      )
    | ATOM a => a
    | LIST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else " ") ^ (pp e))
      in "(" ^ ((fn (_, x) => x) (Vector.foldl f (true, "") l)) ^ ")"
      end
    | FOREST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else "\n") ^ (pp e))
      in (fn (_, x) => x) (Vector.foldl f (true, "") l)
      end

  fun parseClaim (ls: Reader.t vector): t option =
    if Vector.length ls <> 3 then NONE
    else case Vector.sub (ls, 1) of
        Reader.ATOM a =>
          Option.map (fn x => PRIMOP (CLAIM (a, x)))
            (parse (Vector.sub (ls, 2)))
      | _ => NONE

  and parseAlias (ls: Reader.t vector): t option =
    if Vector.length ls <> 3 then NONE
    else case Vector.sub (ls, 1) of
        Reader.ATOM a =>
          Option.map (fn x => PRIMOP (ALIAS (a, x)))
            (parse (Vector.sub (ls, 2)))
      | _ => NONE

  and parse (r: Reader.t): t option =
    case r of
      Reader.FOREST ss =>
        let
          fun f (_, NONE) = NONE
            | f (e, SOME vs) =
              Option.map (fn x => Vector.concat [vs, Vector.fromList [x]])
                (parse e)
        in Option.map (fn x => FOREST x)
          (Vector.foldl f (SOME (Vector.fromList [])) ss)
        end
    | Reader.LIST ls =>
      if Vector.length ls = 0 then SOME (LIST (Vector.fromList []))
      else (
        case Vector.sub (ls, 0) of
          Reader.ATOM "claim" => parseClaim ls
        | Reader.ATOM "alias" => parseAlias ls
        | _ =>
          let
            fun f (_, NONE) = NONE
              | f (e, SOME vs) =
                Option.map (fn x => Vector.concat [vs, Vector.fromList [x]])
                  (parse e)
          in Option.map (fn x => LIST x)
            (Vector.foldl f (SOME (Vector.fromList [])) ls)
          end
      )
    | Reader.ATOM "claim" => NONE
    | Reader.ATOM "alias" => NONE
    | Reader.ATOM a => SOME (ATOM a)
end

fun main () =
  let
    val source = Source.fromStream TextIO.stdIn
    (*
    val prog = Reader.read source
    val repr = case prog of SOME p => Reader.pp p | NONE => "ERROR!!"
    *)
    val parsed = Option.composePartial (Parser.parse, Reader.read) source
    val repr = case parsed of SOME p => Parser.pp p | NONE => "ERROR!!"
  in TextIO.output (TextIO.stdOut, repr ^ "\n")
  end

val _ = main ()
