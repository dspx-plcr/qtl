fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")

infix >>=
structure Result = struct
  datatype ('a, 'b) result = Ok of 'a | Err of 'b

  fun (r: ('a, 'c) result) >>= (f: 'a -> ('b, 'c) result): ('b, 'c) result =
    case r of Ok x => f x | Err e => Err e
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

(* TODO: Consider refactoring this into a functor *)
structure Source = struct
  structure Mark = struct
    type t = { pos: int, line: int, col: int }

    fun new_line { pos = p, line = l, col = c }: t =
      { pos = p + 1, line = l + 1, col = 1 }
    fun advance { pos = p, line = l, col = c }: t =
      { pos = p + 1, line = l, col = c + 1 }
  end

  type token = int
  type t = {
    buf: string,
    point: Mark.t ref,
    marks: (string * Mark.t * token) list ref,
    next_tok: token ref
  }

  type slice = { start: Mark.t, finish: Mark.t }
  exception exc of string
  val succeed_no_start = "internal error: attempting to succeed at reading" ^
    " without having started to read anything"
  val fail_no_start = "internal error: attempting to fail at reading without" ^
    " having started to read anything"
  val big_line_pos = "internal error: attempting to convert pos to line and" ^
    " column when pos is pointing past the end of the buffer"
  val bad_token = "internal error: attempted to remove mark with invalid token"

  fun point (buf: t): Mark.t = !(#point buf)
  fun pos (buf: t): int = #pos (!(#point buf))
  fun line (buf: t): int = #line (!(#point buf))
  fun col (buf: t): int = #col (!(#point buf))
  fun eof (buf: t): bool =
    (String.size (#buf buf) <= 0) orelse (String.size (#buf buf) <= pos buf)
  fun peek (buf: t): char = String.sub (#buf buf, pos buf)
  fun try_peek (buf: t): char option =
    if eof buf then NONE else SOME (peek buf)
  fun advance (buf: t): t =
    case try_peek buf of
      NONE => buf
    | SOME #"\n" => (#point buf := Mark.new_line (point buf); buf)
    | SOME _ => (#point buf := Mark.advance (point buf); buf)
  fun substring (buf: t, i: int, j: int) = String.substring (#buf buf, i, j)

  fun start (buf: t, msg: string): token =
    let val tok = !(#next_tok buf)
    in (
      (#marks buf) := (msg, point buf, tok) :: !(#marks buf);
      (#next_tok buf) := tok + 1;
      tok
    ) end
  fun success (buf: t, tok: token): slice =
    let
      val marks = #marks buf
      val start = case !marks of
          [] => raise exc (succeed_no_start ^
            "\nline: " ^ (Int.toString (line buf)) ^
            ", col: " ^ (Int.toString (col buf)))
        | ((_,p,t)::ms) =>
          if t = tok
          then (marks := ms; p)
          else raise exc (bad_token ^
            "\nexpected: " ^ (Int.toString t) ^
            "\nreceived: " ^ (Int.toString tok))
    in
      (* TODO: check for off by one-ish *)
      { start = start, finish = (point buf) }
    end

  fun expected_token (buf: t, tok: token): bool =
    case !(#marks buf) of
      [] => false
    | (_,_,t)::_ => tok = t

  fun failure (buf: t, tok: token, msg: string): string =
    let
      fun build_msg (res, ms): string = msg
    in case !(#marks buf) of
        [] => raise exc (fail_no_start ^
          "\nline: " ^ (Int.toString (line buf)) ^
          ", col: " ^ (Int.toString (col buf)))
      | (m,p,t)::ms =>
        if t = tok
        then (#marks buf := ms; build_msg ("", !(#marks buf)))
    else raise exc (bad_token ^
      "\nexpected: " ^ (Int.toString t) ^
      "\nreceived: " ^ (Int.toString tok))
    end

  fun fromString (str: string): t =
    { buf = str, point = ref { pos = 0, line = 1, col = 1 }, marks = ref [],
      next_tok = ref 0 }
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

structure Reader :> sig
  type t
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector

  val source: t -> Source.slice
  val item: t -> item
  val read: Source.t -> (t, string) result
  val pp: t -> string
end = struct
  (* TODO: figure out how to only have one definition *)
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector
  withtype t = { source: Source.slice, item: item }

  fun source (t: t) = #source t
  fun item (t: t) = #item t

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

structure Parser :> sig
  type t

  val pp: t -> string
  val parse: Reader.t -> (t, string) result
end = struct
  datatype item =
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
  withtype t = { source: Source.slice, item: item }

  fun pp (p: t): string =
    case #item p of
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

  fun error (it: Reader.t, err: string): ('a, string) result =
    let
      val start = #start (Reader.source it)
      val finish = #finish (Reader.source it)
      val sl = Int.toString (#line start)
      val sc = Int.toString (#col start)
      val fl = Int.toString (#line finish)
      val fc = Int.toString (#col finish)
    in Err (sl ^ ":" ^ sc ^ "-" ^ fl ^ ":" ^ fc ^ " error: " ^ err)
    end

  fun parseClaim (ls: Reader.t vector): (t, string) result =
    if Vector.length ls <> 3
    then error (Vector.sub (ls, 0), "CLAIM must have exactly 2 arguments")
    else let
        val tok = Vector.sub (ls, 0)
        val id = Vector.sub (ls, 1)
        val expr = Vector.sub (ls, 2)
      in case Reader.item id of
          Reader.ATOM a => parse expr >>= (fn x =>
            Ok { source = Reader.source tok, item = PRIMOP (CLAIM (a, x)) })
        | _ => error (id, "first argument of CLAIM must be an identifier")
      end

  and parseAlias (ls: Reader.t vector): (t, string) result =
    if Vector.length ls <> 3
    then error (Vector.sub (ls, 0), "ALIAS must have exactly 2 arguments")
    else let
        val tok = Vector.sub (ls, 0)
        val id = Vector.sub (ls, 1)
        val expr = Vector.sub (ls, 2)
      in case Reader.item id of
          Reader.ATOM a => parse expr >>= (fn x =>
            Ok { source = Reader.source tok, item = PRIMOP (ALIAS (a, x)) })
        | _ => error (id, "first argument of ALIAS must be an identifier")
      end

  and parse (r: Reader.t): (t, string) result =
    case Reader.item r of
      Reader.FOREST ss =>
        let
          fun f (_, Err e): (t vector, string) result = Err e
            | f (r, Ok rs) =
              parse r >>= (fn x => Ok (Vector.concat [rs, Vector.fromList [x]]))
          val init = Ok (Vector.fromList [])
        in Vector.foldl f init ss >>=
          (fn x => Ok { source = Reader.source r, item = FOREST x })
        end
    | Reader.LIST ls =>
      if Vector.length ls = 0
      then Ok { source = Reader.source r, item = LIST (Vector.fromList []) }
      else (
        case Reader.item (Vector.sub (ls, 0)) of
          Reader.ATOM "claim" => parseClaim ls
        | Reader.ATOM "alias" => parseAlias ls
        | _ =>
          let
            fun f (_, Err e) = Err e
              | f (e, Ok vs) = parse e >>=
                (fn x => Ok (Vector.concat [vs, Vector.fromList [x]]))
            val init = Ok (Vector.fromList [])
          in Vector.foldl f init ls >>=
            (fn x => Ok { source = Reader.source r, item = LIST x })
          end
      )
    | Reader.ATOM "claim" => error (r, "CLAIM must be used as a function")
    | Reader.ATOM "alias" => error (r, "ALIAS must be used as a function")
    | Reader.ATOM a => Ok { source = Reader.source r, item = ATOM a }
end

fun main () =
  let
    val source = Source.fromStream TextIO.stdIn
    (*
    val prog = Reader.read source
    val repr = case prog of Ok p => Reader.pp p | Err e => e
    *)
    val parsed = (Reader.read source) >>= Parser.parse
    val repr = case parsed of Ok p => Parser.pp p | Err e => e
  in TextIO.output (TextIO.stdOut, repr ^ "\n")
  end

val _ = main ()
