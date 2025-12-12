open PAst

module Make(P:ParserExt) : sig
    val parse_expr_file : string -> P.E.pexpr
    val parse_expr_string : string -> P.E.pexpr

    val parse_program_file : string -> P.E.program
    val parse_program_string : string -> P.E.program
end
