{
  open Lexing
  open Ast
  open Parser

  exception Lexing_error of string

  let id_or_kwd =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      [ "module", MODULE; "interface", INTERFACE; "type", TYPE;
        "val", VAL; "invariant", INVARIANT; "end", END;
        "match", MATCH; "with", WITH; "map", MAP;
        "axiom", AXIOM;
        "true", CST (Cbool true);
        "false", CST (Cbool false);
        "None", CST Cnone ];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s

  let string_buffer = Buffer.create 1024
}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = (letter | '_') (letter | digit | '_')*
let integer = '0' | ['1'-'9'] digit*
let space = ' ' | '\t'
let comment = "//" [^'\n']*

rule next_token = parse
  | '\n'      { new_line lexbuf; next_token lexbuf }
  | (space | comment)+    
              { next_token lexbuf }
  | ident as id { id_or_kwd id }
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '*'       { TIMES }
  | '/'       { DIV }
  | "=="      { EQ }
  | "!="      { NEQ }
  | "<"       { LT }
  | "<="      { LE }
  | ">"       { GT }
  | ">="      { GE }
  | "&&"      { AND }
  | "||"      { OR }
  | '('       { LP }
  | ')'       { RP }
  | '{'       { LB }
  | '}'       { RB }
  | ','       { COMMA }
  | '='       { EQUAL }
  | ':'       { COLON }
  | '.'       { DOT }
  | '|'       { BAR }
  | "->"      { ARROW }
  | integer as s
              { try CST (Cint (Int64.of_string s))
                with _ -> raise (Lexing_error ("constant too large: " ^ s)) }
  | '"'       { CST (Cstring (string lexbuf)) }
  | "[@proof]" { PROOF }
  | "[@" { VFX_ATTR (vfx_attr lexbuf) }
  | eof       { EOF }
  | _ as c    { raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }

and vfx_attr = parse
  | "" { vfx_attr_content (Buffer.create 16) 1 lexbuf }

and vfx_attr_content buf depth = parse
  | '[' {
      Buffer.add_char buf '[';
      vfx_attr_content buf (depth + 1) lexbuf
    }
  | ']' {
      if depth = 1 then
        Buffer.contents buf
      else begin
        Buffer.add_char buf ']';
        vfx_attr_content buf (depth - 1) lexbuf
      end
    }
  | _ as c {
      Buffer.add_char buf c;
      vfx_attr_content buf depth lexbuf
    }
  | eof { raise (Lexing_error "attribute [@...] not closed") }

and string = parse
  | '"'
      { let s = Buffer.contents string_buffer in
    Buffer.reset string_buffer;
    s }
  | "\\n"
      { Buffer.add_char string_buffer '\n';
    string lexbuf }
  | "\\\""
      { Buffer.add_char string_buffer '"';
    string lexbuf }
  | _ as c
      { Buffer.add_char string_buffer c;
    string lexbuf }
  | eof
      { raise (Lexing_error "unterminated string") }
