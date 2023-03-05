#use "pc.ml";;
#use "list.ml";;


exception EINGAFROUR;;
exception X_this_should_not_happen of string;;

let rec is_member a = function
  | [] -> false
  | a' :: s -> (a = a') || (is_member a s);;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
  val nt_sexpr : sexpr PC.parser
  val scheme_sexpr_list_of_sexpr_list : sexpr list -> sexpr
end;; (* end of READER signature *)

module Reader : READER = struct
  open PC;;

  type string_part =
    | Static of string
    | Dynamic of sexpr;;

  let unitify nt = pack nt (fun _ -> ());;

  let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input in
    let nt1 = disj nt1 nt2 in
    nt1 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = 
    let nt1 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
    let nt2 = disj nt1 (unitify (one_of "{}")) in
    let nt3 = diff nt_any nt2 in
    let nt3 = unitify nt3 in
    let nt3 = disj nt3 nt1 in
    let nt3 = star nt3 in
    let nt1 = unitify (caten (char '{') (caten nt3 (char '}'))) in
    nt1 str
  and nt_sexpr_comment str = 
    let nt1 = word "#;" in
    let nt1 = caten nt1 nt_sexpr in
    let nt1 = unitify nt1 in
    nt1 str  
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str
  and nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str
  and make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str = 
    let nt1 = range '0' '9' in
    let nt1 = pack nt1 (fun (ch) -> (int_of_char ch) - 48) in
    nt1 str
  and nt_hex_digit str = 
    let nt1 = range '0' '9' in
    let nt1 = pack nt1 (fun (ch) -> (int_of_char ch) - 48) in
    let nt2 = range 'a' 'f' in 
    let nt2 = pack nt2 (fun (ch) -> (int_of_char ch) - 87) in
    let nt3 = disj nt1 nt2 in 
    nt3 str

  and nt_nat str = 
    let nt1 = plus (range '0' '9') in
      let nt1 = pack nt1 
        (fun res -> (int_of_string (string_of_list res))) in
        nt1 str


  and nt_hex_nat str = 
    let nt1 = plus nt_hex_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit ->
                      16 * num + digit)
                    0
                    digits) in
    nt1 str

  and nt_optional_sign str = 
    let nt1 = (maybe (one_of "+-")) in 
      let nt1 = pack nt1 
        (fun (ch) ->
          match ch with
          | None -> true
          | Some('+') -> true
          | _ -> false) in
      nt1 str
      

  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and make_maybe nt none_value =
    pack (maybe nt)
      (function
       | None -> none_value
       | Some(x) -> x)

  and nt_floatA str =
    let nt1 = caten nt_integer_part (char '.') in
    let nt1 = caten nt1 (maybe nt_mantissa) in 
    let nt1 = caten nt1 (maybe nt_exponent) in
    let nt1 = pack nt1 (fun ((((num, _), man), exp)) -> 
      match man, exp with
      | None, None -> num 
      (* (float_of_string (num^".")) *)
      | Some(m), None -> num +. m
        (* (float_of_string (num^"."^man)) *)
      | None, Some(x) -> num *. x
        (* (float_of_string (num^".")) *. exp  *)
      | Some(m), Some(x) -> (num +. m) *. x) in
        (* (float_of_string (num^"."^man)) *. exp) in *)
    nt1 str

  and nt_floatB str = 
    let nt1 = caten (char '.') nt_mantissa in
    let nt1 = caten nt1 (maybe nt_exponent) in
    let nt1 = pack nt1 (fun (((_, man), exp)) ->
      match exp with
      | None -> man
        (* float_of_string ("."^man) *)
      | Some(x) -> man *. x) in
        (* (float_of_string ("."^man)) *. exp) in *)
    nt1 str

  and nt_floatC str = 
    let nt1 = caten nt_integer_part nt_exponent in
    let nt1 = pack nt1 (fun ((num, exp)) -> num *. exp) in
      nt1 str


  and nt_float str = 
    let nt1 = nt_optional_sign in 
    let nt1 = caten nt1 (disj_list [nt_floatA ; nt_floatB ; nt_floatC]) in
    let nt1 = pack nt1 (fun (is_positive, f) -> 
      match is_positive with
      | true -> ScmReal(f)
      | false -> ScmReal(-.f)) in
    nt1 str

  and nt_number str =
    let nt1 = nt_float in
    let nt2 = nt_frac in
    let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in 
    let nt1 = disj nt1 (disj nt2 nt3) in
    let nt1 = pack nt1 (fun r -> ScmNumber r) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str  
  and nt_boolean str =
    let nt1 = char '#' in
    let nt2 = char_ci 'f' in
    let nt2 = pack nt2 (fun _ -> ScmBoolean false) in
    let nt3 = char_ci 't' in
    let nt3 = pack nt3 (fun _ -> ScmBoolean true) in
    let nt2 = disj nt2 nt3 in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, value) -> value) in
    let nt2 = nt_symbol_char in
    let nt1 = not_followed_by nt1 nt2 in
    nt1 str
  and nt_char_simple str =
    let nt1 = const(fun ch -> ' ' < ch) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str

  and nt_char_named str = 
    let nl = pack (word "newline") (fun (_) -> char_of_int 10) in
    let nul = pack (word "nul") (fun (_) -> char_of_int 0) in 
    let p = pack (word "page") (fun (_) -> char_of_int 12) in 
    let ret = pack (word "return") (fun (_) -> char_of_int 13) in 
    let sp = pack (word "space") (fun (_) -> char_of_int 32) in 
    let t = pack (word "tab") (fun (_) -> char_of_int 9) in 
    let nt1 = disj_list [nl;nul;p;ret;sp;t] in
    nt1 str

  and nt_char_hex str =
    let nt1 = caten (char_ci 'x') nt_hex_nat in
    let nt1 = pack nt1 (fun (_, n) -> n) in
    let nt1 = only_if nt1 (fun n -> n < 256) in
    let nt1 = pack nt1 (fun n -> char_of_int n) in
    nt1 str  
  and nt_char str =
    let nt1 = word "#\\" in
    let nt2 = disj nt_char_simple (disj nt_char_named nt_char_hex) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, ch) -> ScmChar ch) in
    nt1 str
  and nt_symbol_char str =
    let nt1 = range_ci 'a' 'z' in
    let nt1 = pack nt1 Char.lowercase_ascii in
    let nt2 = range '0' '9' in
    let nt3 = one_of "!$^*_-+=<>?/" in
    let nt1 = disj nt1 (disj nt2 nt3) in
    nt1 str
  and nt_symbol str = 
    let nt1 = plus nt_symbol_char in
    let nt1 = pack nt1 (fun (lst)-> ScmSymbol(string_of_list lst)) in 
    nt1 str

  and nt_string_part_simple str =
    let nt1 =
      disj_list [unitify (char '"'); unitify (char '\\'); unitify (word "~~");
                 unitify nt_string_part_dynamic] in
    let nt1 = diff nt_any nt1 in
    nt1 str
  and nt_string_part_meta str =
    let nt1 =
      disj_list [pack (word "\\\\") (fun _ -> '\\');
                 pack (word "\\\"") (fun _ -> '"');
                 pack (word "\\n") (fun _ -> '\n');
                 pack (word "\\r") (fun _ -> '\r');
                 pack (word "\\f") (fun _ -> '\012');
                 pack (word "\\t") (fun _ -> '\t');
                 pack (word "~~") (fun _ -> '~')] in
    nt1 str
  and nt_string_part_hex str =
    let nt1 = word_ci "\\x" in
    let nt2 = nt_hex_nat in
    let nt2 = only_if nt2 (fun n -> n < 256) in
    let nt3 = char ';' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (n, _)) -> n) in
    let nt1 = pack nt1 char_of_int in
    nt1 str
  and nt_string_part_dynamic str = 
    let nt1 = word "~{" in 
    (* let nt3 = star (diff nt_any (char '}')) in
    let nt3 = pack nt3 (fun lst -> string_of_list lst) in *)
    let nt2 = caten (caten nt1 nt_sexpr) (char '}') in
    let nt2 = pack nt2 (fun ((_, exp), _) -> Dynamic(ScmPair(ScmSymbol("format"), ScmPair(ScmString("~a"), ScmPair(exp, ScmNil))))) in
    (* let nt2 = pack nt2 (fun (_, s) -> Dynamic s) in  *)
    nt2 str

  and nt_string_part_static str =
    let nt1 = disj_list [nt_string_part_simple;
                         nt_string_part_meta;
                         nt_string_part_hex] in
    let nt1 = plus nt1 in
    let nt1 = pack nt1 string_of_list in
    let nt1 = pack nt1 (fun str -> Static str) in
    nt1 str
  and nt_string_part str =
    disj nt_string_part_static nt_string_part_dynamic str
  and nt_string str =
    let nt1 = char '"' in
    let nt2 = star nt_string_part in
    let nt3 = char '"' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (parts, _)) -> parts) in
    let nt1 = pack nt1
                (fun parts ->
                  match parts with
                  | [] -> ScmString ""
                  | [Static(str)] -> ScmString str
                  | [Dynamic(sexpr)] -> sexpr
                  | parts ->
                      let argl =
                      List.fold_right
                        (fun car cdr ->
                          ScmPair((match car with
                                  | Static(str) -> ScmString(str)
                                  | Dynamic(sexpr) -> sexpr),
                                  cdr))
                        parts
                        ScmNil in
                     ScmPair(ScmSymbol "string-append", argl)) in
    nt1 str
  and nt_vector str = 
    let nt1 = unitify (caten (word "#(") (star nt_whitespace)) in 
    let nt1 = caten nt1 (star nt_sexpr) in 
    let nt2 = caten nt1 (unitify (char ')')) in 
    let nt2 = pack nt2 (fun ((_,lst),_) -> ScmVector(lst)) in
    nt2 str

  and real_helper lst = 
  let rec realHelper = fun (lst) ->
      match (List.length lst) with 
        | 0 -> ScmNil
        | 1 -> hd lst
        | n -> ScmPair (hd lst , realHelper (tl lst)) in 
      realHelper lst 
  (* 
  proper:
  (a . b c) ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair( ScmSymbol "c", ScmNil)) )
  (a  b  c) ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair( ScmSymbol "c", ScmNil)) )
  
  inproper:
  (a b . c) ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmSymbol "c"))
    *)
  and nt_list str = 
    let ntAtrala = char '(' in 
    let ntSof = char ')' in
    let ntProper = caten (star nt_sexpr) ntSof in
    let ntProper = pack ntProper (fun (sexps,_) -> sexps @ [ScmNil]) in 

    let ntUnproper = caten (plus nt_sexpr) (char '.') in
    let ntx = caten (star nt_whitespace) (caten nt_sexpr ntSof) in
    let ntUnproper = not_followed_by ntUnproper ntx in
    let ntUnproper = pack ntUnproper (fun (sexps, _) -> sexps) in
    let ntUnproper = star ntUnproper in
    let ntUnproper = pack ntUnproper (fun (sexp)-> List.flatten sexp) in 

    let nt1 = caten ntUnproper (caten (plus nt_sexpr) (caten (char '.') ntx)) in
    let nt1 = pack nt1 (fun (sexps1,(sexps2, (_, (_,(item,_)))))-> sexps1 @ sexps2 @ [item]) in 

    let nt2 = caten (caten ntUnproper (caten nt_sexpr (plus nt_sexpr))) ntSof in 
    let nt2 = pack nt2 (fun ((sexps1, (exp, sexps2)),_) -> sexps1 @ [exp] @ sexps2 @ [ScmNil]) in

    let ntssss = disj_list [ntProper ; nt1 ; nt2] in
    let ntssss = caten ntAtrala ntssss in 
    let ntssss = pack ntssss (fun (_, sexps) -> real_helper sexps)in
    ntssss str

                          
  and make_quoted_form nt_qf qf_name =
    let nt1 = caten nt_qf nt_sexpr in
    let nt1 = pack nt1
                (fun (_, sexpr) ->
                  ScmPair(ScmSymbol qf_name,
                          ScmPair(sexpr, ScmNil))) in
    nt1
  and nt_quoted_forms str =
    let nt1 =
      disj_list [(make_quoted_form (unitify (char '\'')) "quote");
                 (make_quoted_form (unitify (char '`')) "quasiquote");
                 (make_quoted_form
                    (unitify (not_followed_by (char ',') (char '@')))
                    "unquote");
                 (make_quoted_form (unitify (word ",@")) "unquote-splicing")] in
    nt1 str
  and nt_sexpr str = 
    let nt1 =
        disj_list [nt_void; nt_number; nt_boolean; nt_char; nt_symbol;
                  nt_string; nt_vector; nt_list; nt_quoted_forms] in
    let nt1 = make_skipped_star nt1 in
    nt1 str;;



  let scheme_sexpr_list_of_sexpr_list sexprs =
    List.fold_right (fun car cdr -> ScmPair (car, cdr)) sexprs ScmNil;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
| ScmVoid -> "#<void>"
| ScmNil -> "()"
| ScmBoolean(false) -> "#f"
| ScmBoolean(true) -> "#t"
| ScmChar('\n') -> "#\\newline"
| ScmChar('\r') -> "#\\return"
| ScmChar('\012') -> "#\\page"
| ScmChar('\t') -> "#\\tab"
| ScmChar(' ') -> "#\\space"
| ScmChar(ch) ->
   if (ch < ' ')
   then let n = int_of_char ch in
        Printf.sprintf "#\\x%x" n
   else Printf.sprintf "#\\%c" ch
| ScmString(str) ->
   Printf.sprintf "\"%s\""
     (String.concat ""
        (List.map
           (function
            | '\n' -> "\\n"
            | '\012' -> "\\f"
            | '\r' -> "\\r"
            | '\t' -> "\\t"
            | '\"' -> "\\\""
            | ch ->
               if (ch < ' ')
               then Printf.sprintf "\\x%x;" (int_of_char ch)
               else Printf.sprintf "%c" ch)
           (list_of_string str)))
| ScmSymbol(sym) -> sym
| ScmNumber(ScmRational(0, _)) -> "0"
| ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
| ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
| ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
| ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
| ScmVector(sexprs) ->
   let strings = List.map string_of_sexpr sexprs in
   let inner_string = String.concat " " strings in
   Printf.sprintf "#(%s)" inner_string
| ScmPair(ScmSymbol "quote",
          ScmPair(sexpr, ScmNil)) ->
   Printf.sprintf "'%s" (string_of_sexpr sexpr)
| ScmPair(ScmSymbol "quasiquote",
          ScmPair(sexpr, ScmNil)) ->
   Printf.sprintf "`%s" (string_of_sexpr sexpr)
| ScmPair(ScmSymbol "unquote",
          ScmPair(sexpr, ScmNil)) ->
   Printf.sprintf ",%s" (string_of_sexpr sexpr)
| ScmPair(ScmSymbol "unquote-splicing",
          ScmPair(sexpr, ScmNil)) ->
   Printf.sprintf ",@%s" (string_of_sexpr sexpr)
| ScmPair(car, cdr) ->
   string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
| ScmNil -> Printf.sprintf "(%s)" car_string
| ScmPair(cadr, cddr) ->
   let new_car_string =
     Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
   string_of_sexpr' new_car_string cddr
| cdr ->
   let cdr_string = (string_of_sexpr cdr) in
   Printf.sprintf "(%s . %s)" car_string cdr_string;;

let print_sexpr chan sexpr = output_string chan (string_of_sexpr sexpr);;

let print_sexprs chan sexprs =
output_string chan
  (Printf.sprintf "[%s]"
     (String.concat "; "
        (List.map string_of_sexpr sexprs)));;

let sprint_sexpr _ sexpr = string_of_sexpr sexpr;;

let sprint_sexprs chan sexprs =
Printf.sprintf "[%s]"
  (String.concat "; "
     (List.map string_of_sexpr sexprs));;
