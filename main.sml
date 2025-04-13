fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")

structure Result = struct
  datatype ('a, 'b) result = Ok of 'a | Err of 'b
end

open Result

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
  type token = int
  type t = {
    buf: string,
    pos: int ref,
    marks: (string * int * token) list ref,
    next_tok: int ref
  }

  type slice = { start: int, len: int }
  exception exc of string
  val succeed_no_start = "internal error: attempting to succeed at reading" ^
    " without having started to read anything"
  val fail_no_start = "internal error: attempting to fail at reading without" ^
    " having started to read anything"
  val big_line_pos = "internal error: attempting to convert pos to line and" ^
    " column when pos is pointing past the end of the buffer"
  val bad_token = "internal error: attempted to remove mark with invalid token"

  fun eof (buf: t): bool =
    (String.size (#buf buf) <= 0) orelse (String.size (#buf buf) <= !(#pos buf))
  fun pos (buf: t): int = !(#pos buf)
  fun peek (buf: t): char = String.sub (#buf buf, !(#pos buf))
  fun try_peek (buf: t): char option =
    if eof buf then NONE else SOME (peek buf)
  fun advance (buf: t): t = ((#pos buf) := !(#pos buf) + 1; buf)
  fun substring (buf: t, i: int, j: int) = String.substring (#buf buf, i, j)

  fun line_col ({ buf = buf, pos = pos, marks = marks, next_tok = _ }: t)
    : int * int =
    let
      fun make_marks (ms, res) =
        case ms of
          [] => res
        | (s,p,t)::ms' =>
          let val res' = (res ^ "\n" ^ (Int.toString p) ^ ": " ^ s)
          in make_marks (ms', res')
          end
      fun helper (l, l', p) =
        if p = !pos then (l, p - l')
        else if String.sub (buf, p) = #"\n" then helper (l+1, p+1, p+1)
        else helper (l, l', p+1)
    in
      if String.size buf <= !pos
      then raise exc (big_line_pos ^
        "\nbuf size: " ^ (Int.toString (String.size buf)) ^
        "\npos: " ^ (Int.toString (!pos)) ^
        "\nmarks:\n" ^ (make_marks (!marks, "")))
      else helper (1, 0, 0)
    end

  fun start (buf: t, msg: string): token =
    let val tok = !(#next_tok buf)
    in (
      (#marks buf) := (msg, !(#pos buf), tok) :: !(#marks buf);
      (#next_tok buf) := tok + 1;
      tok
    ) end
  fun success (buf: t, tok: token): slice =
    let
      val marks = #marks buf
      val start = case !marks of
          [] =>
            let val (line, col) = line_col buf
          in raise exc (succeed_no_start ^
            "\nline: " ^ (Int.toString line) ^
                ", col: " ^ (Int.toString col))
            end
        | ((_,p,t)::ms) =>
          if t = tok
          then (marks := ms; p)
          else raise exc (bad_token ^
            "\nexpected: " ^ (Int.toString t) ^
            "\nreceived: " ^ (Int.toString tok))
    in
      (* TODO: check for off by one-ish *)
      { start = start, len = !(#pos buf) - start - 1 }
    end

  fun expected_token (buf: t, tok: token): bool =
    case !(#marks buf) of
      [] => false
    | (_,_,t)::_ => tok = t

  fun failure (buf: t, tok: token, msg: string): string =
    let
      fun build_msg (res, ms): string = msg
    in case !(#marks buf) of
        [] => 
        let val (line, col) = line_col buf
        in raise exc (fail_no_start ^
            "\nline: " ^ (Int.toString line) ^
            ", col: " ^ (Int.toString col))
        end
      | (m,p,t)::ms =>
        if t = tok
        then (#marks buf := ms; build_msg ("", !(#marks buf)))
    else raise exc (bad_token ^
      "\nexpected: " ^ (Int.toString t) ^
      "\nreceived: " ^ (Int.toString tok))
    end

  fun fromString (str: string): t =
    { buf = str, pos = ref 0, marks = ref [], next_tok = ref 0 }
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
  type t
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector

  val read: Source.t -> (t, string) result
  val pp: t -> string
end = struct
  (* TODO: figure out how to only have one definition *)
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector
  withtype t = { source: Source.slice, item: item }


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
    case #item e of
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
        val tok = Source.start (buf, "reading an atom")
        fun helper n =
          case Source.try_peek buf of
            NONE => {
              source = Source.success (buf, tok),
              item = ATOM (Source.substring (buf, start, n))
            }
          | SOME c =>
            if isAtomChar c
            then (Source.advance buf; helper (n + 1))
            else {
              source = Source.success (buf, tok),
              item = ATOM (Source.substring (buf, start, n))
            }
      in helper 0
      end

    and readList (buf: Source.t): (t, string) result =
      let
        val tok = Source.start (buf, "reading a list")
        fun helper res =
          case Source.try_peek buf of
            NONE => Err (Source.failure (buf, tok, "couldn't find list end"))
          | SOME #")" =>
            (Source.advance buf; Ok {
              source = Source.success (buf, tok),
              item = LIST (Vector.fromList (List.rev res))
            })
          | _ => case readHelper buf of
              NONE => Err (Source.failure (buf, tok, "couldn't find list end"))
            | SOME r => case r of
                Err e => Err (Source.failure (buf, tok, e))
              | Ok v => helper (v :: res)
      in (Source.advance buf; helper [])
      end

    and readForest (res: t list) (buf: Source.t): (t, string) result =
      let
        (* TODO: better terminology *)
        val tok = Source.start (buf, "reading forest");
      in
        case readHelper buf of
          NONE => Ok {
            source = Source.success (buf, tok),
            item = FOREST (Vector.fromList (List.rev res))
          }
        | SOME r => case r of
          Err e => Err (Source.failure (buf, tok, e))
        | Ok v => readForest (v :: res) buf
      end

    and readHelper (buf: Source.t): (t, string) result option =
      if Source.eof buf then NONE
      else case Source.peek buf of
        #"(" => SOME (readList buf)
      | c =>
        if isWhitespace c then readHelper (Source.advance buf)
        else if isAtomChar c then SOME (Ok (readAtom buf))
        else SOME (Err "unexpected character")
  in
    val read = readForest []
  end
end

(*
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
*)

fun main () =
  let
    val source = Source.fromStream TextIO.stdIn
    val prog = Reader.read source
    val repr = case prog of Ok p => Reader.pp p | Err e => e
    (*
    val parsed = Option.composePartial (Parser.parse, Reader.read) source
    val repr = case parsed of SOME p => Parser.pp p | NONE => "ERROR!!"
    *)
  in TextIO.output (TextIO.stdOut, repr ^ "\n")
  end

val _ = main ()
