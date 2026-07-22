open Compiler_extracted

let rec coq_list_of_list = function
  | [] -> Nil
  | x :: xs -> Cons (x, coq_list_of_list xs)

let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 0 then XO (pos_of_int (n lsr 1))
  else XI (pos_of_int (n lsr 1))

let z_of_int n = if n = 0 then Z0 else Zpos (pos_of_int n)

let rec int_of_pos = function
  | XH -> 1
  | XO p -> 2 * int_of_pos p
  | XI p -> 2 * int_of_pos p + 1

let string_of_z = function
  | Z0 -> "0"
  | Zpos p -> string_of_int (int_of_pos p)
  | Zneg p -> "-" ^ string_of_int (int_of_pos p)

let reg64 = function
  | RAX -> "%rax" | RBX -> "%rbx" | RCX -> "%rcx" | RDX -> "%rdx"
  | RSI -> "%rsi" | RDI -> "%rdi" | RBP -> "%rbp" | RSP -> "%rsp"
  | R8 -> "%r8" | R9 -> "%r9" | R10 -> "%r10" | R11 -> "%r11"
  | R12 -> "%r12" | R13 -> "%r13" | R14 -> "%r14" | R15 -> "%r15"

let reg32 = function
  | RAX -> "%eax" | RBX -> "%ebx" | RCX -> "%ecx" | RDX -> "%edx"
  | RSI -> "%esi" | RDI -> "%edi" | RBP -> "%ebp" | RSP -> "%esp"
  | R8 -> "%r8d" | R9 -> "%r9d" | R10 -> "%r10d" | R11 -> "%r11d"
  | R12 -> "%r12d" | R13 -> "%r13d" | R14 -> "%r14d" | R15 -> "%r15d"

let cond_name = function
  | Cond_e -> "e"
  | Cond_ne -> "ne"
  | Cond_b -> "b"
  | Cond_be -> "be"
  | Cond_ae -> "ae"
  | Cond_a -> "a"
  | Cond_l -> "l"
  | Cond_le -> "le"
  | Cond_ge -> "ge"
  | Cond_g -> "g"
  | Cond_p -> "p"
  | Cond_np -> "np"

let label_name l = Printf.sprintf ".L%d" (int_of_pos l)

let addr = function
  | Addrmode (Some base, None, Inl ofs) ->
      let ofs_s = string_of_z ofs in
      if ofs_s = "0" then Printf.sprintf "(%s)" (reg64 base)
      else Printf.sprintf "%s(%s)" ofs_s (reg64 base)
  | _ -> failwith "Unsupported addressing mode in emitter"

let align16_minus_call z =
  let n = int_of_string (string_of_z z) in
  (((n + 15) / 16) * 16) - 8

let emit_allocframe oc sz ofs_link =
  let sz_adj = align16_minus_call sz in
  let full = sz_adj + 8 in
  Printf.fprintf oc "\tsubq\t$%d, %%rsp\n" sz_adj;
  Printf.fprintf oc "\tleaq\t%d(%%rsp), %%rax\n" full;
  Printf.fprintf oc "\tmovq\t%%rax, %s(%%rsp)\n" (string_of_z ofs_link)

let emit_freeframe oc sz =
  let sz_adj = align16_minus_call sz in
  Printf.fprintf oc "\taddq\t$%d, %%rsp\n" sz_adj

let emit_instr oc = function
  | Pleaq (rd, a) ->
      Printf.fprintf oc "\tleaq\t%s, %s\n" (addr a) (reg64 rd)
  | Pcmpq_rr (r1, r2) ->
      Printf.fprintf oc "\tcmpq\t%s, %s\n" (reg64 r2) (reg64 r1)
  | Pcmpq_ri (r1, n) ->
      Printf.fprintf oc "\tcmpq\t$%s, %s\n" (string_of_z n) (reg64 r1)
  | Pjcc (c, l) ->
      Printf.fprintf oc "\tj%s\t%s\n" (cond_name c) (label_name l)
  | Pmovl_rm (rd, a) ->
      Printf.fprintf oc "\tmovl\t%s, %s\n" (addr a) (reg32 rd)
  | Pmovl_mr (a, rs) ->
      Printf.fprintf oc "\tmovl\t%s, %s\n" (reg32 rs) (addr a)
  | Pbswap32 rd ->
      Printf.fprintf oc "\tbswap\t%s\n" (reg32 rd)
  | Paddq_ri (rd, n) ->
      Printf.fprintf oc "\taddq\t$%s, %s\n" (string_of_z n) (reg64 rd)
  | Psubq_ri (rd, n) ->
      Printf.fprintf oc "\tsubq\t$%s, %s\n" (string_of_z n) (reg64 rd)
  | Psubl_rr (rd, r1) ->
      Printf.fprintf oc "\tsubl\t%s, %s\n" (reg32 r1) (reg32 rd)
  | Paddl_rr (rd, r1) ->
      Printf.fprintf oc "\taddl\t%s, %s\n" (reg32 r1) (reg32 rd)
  | Padcl_rr (rd, r1) ->
      Printf.fprintf oc "\tadcl\t%s, %s\n" (reg32 r1) (reg32 rd)
  | Psbbl_rr (rd, r1) ->
      Printf.fprintf oc "\tsbbl\t%s, %s\n" (reg32 r1) (reg32 rd)
  | Pxorl_r rd ->
      Printf.fprintf oc "\txorl\t%s, %s\n" (reg32 rd) (reg32 rd)
  | Porl_rr (rd, r1) ->
      Printf.fprintf oc "\torl\t%s, %s\n" (reg32 r1) (reg32 rd)
  | Ptestl_rr (r1, r2) ->
      Printf.fprintf oc "\ttestl\t%s, %s\n" (reg32 r2) (reg32 r1)
  | Pcmpl_ri (r1, n) ->
      Printf.fprintf oc "\tcmpl\t$%s, %s\n" (string_of_z n) (reg32 r1)
  | Pjmp_l l ->
      Printf.fprintf oc "\tjmp\t%s\n" (label_name l)
  | Plabel l ->
      Printf.fprintf oc "%s:\n" (label_name l)
  | Pallocframe (sz, _ofs_ra, ofs_link) ->
      emit_allocframe oc sz ofs_link
  | Pfreeframe (sz, _ofs_ra, _ofs_link) ->
      emit_freeframe oc sz
  | Pret ->
      Printf.fprintf oc "\tret\n"
  | _ ->
      failwith "Unsupported instruction in emitter"

let rec iter_coq_list f = function
  | Nil -> ()
  | Cons (x, xs) ->
      f x;
      iter_coq_list f xs

let read_bytes path =
  let ic = open_in_bin path in
  let rec loop acc =
    match input_byte ic with
    | b -> loop (z_of_int b :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
  loop []

let symbol_for_platform sym =
  let is_macos = Sys.command "uname | grep -qi Darwin" = 0 in
  if is_macos then "_" ^ sym else sym

let usage () =
  Printf.eprintf "Usage: emit_f <bytecode.bin> <output.s> [symbol]\n";
  exit 2

let () =
  if Array.length Sys.argv < 3 then usage ();
  let input_path = Sys.argv.(1) in
  let output_path = Sys.argv.(2) in
  let symbol = if Array.length Sys.argv >= 4 then Sys.argv.(3) else "f" in
  let bytes = read_bytes input_path in
  let coq_bytes = coq_list_of_list bytes in
  match transl_bytes coq_bytes with
  | Rejected _ ->
      prerr_endline "Bytecode parser rejected input";
      exit 1
  | Parsed fn ->
      let oc = open_out output_path in
      let sym = symbol_for_platform symbol in
      Printf.fprintf oc "\t.text\n";
      Printf.fprintf oc "\t.globl %s\n" sym;
      Printf.fprintf oc "%s:\n" sym;
      iter_coq_list (emit_instr oc) fn.fn_code;
      close_out oc
