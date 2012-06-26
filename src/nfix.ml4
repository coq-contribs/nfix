(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Pcoq
open Pp
open Flags
open Constrexpr
open Constrexpr_ops
open Topconstr
open Nameops

let pr_nbinder (idl,c) =
  str "(" ++ pr_sequence Nameops.pr_id idl ++ spc () ++
    str ": " ++ Ppconstr.pr_lconstr_expr c ++ str ")"

VERNAC ARGUMENT EXTEND nbinder
PRINTED BY pr_nbinder
    [ "(" ne_ident_list(idl) ":" lconstr(c)  ")"] -> [ (idl,c) ]
END

let pr_nfix_definition (id,bl,type_,def) =
  Nameops.pr_id id ++ spc () ++
    pr_sequence pr_nbinder bl ++ spc () ++ str ":" ++ spc () ++
    Ppconstr.pr_lconstr_expr type_ ++ str " :=" ++ spc () ++
    Ppconstr.pr_lconstr_expr def

VERNAC ARGUMENT EXTEND nfix_definition
PRINTED BY pr_nfix_definition
 [ ident(id)  nbinder_list(bl) ":" lconstr(type_) ":=" lconstr(def)] ->
    [ (id,bl,type_,def) ]
      END

let hole = CHole (Loc.ghost, None)
let dl id = Loc.ghost, id

let rec split_at n l =
  match n with
    | 0 -> [], l
    | n ->
	match l with
	  | a::q ->
	      let (l1, l2) = split_at (n-1) q
	      in (a::l1, l2)
	  | [] -> failwith "split_at"

let mk_binder (idl,c) =
  LocalRawAssum (List.map (fun id -> dl (Names.Name id)) idl,
		 default_binder_kind,
		 c)

(* à la v8.2... *)
let declare_definition
    id (loc, def_obj_kind)
    binder_list red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  Command.do_definition
  id (loc, def_obj_kind) binder_list red_expr_opt constr_expr
  constr_expr_opt decl_hook

(* [abstract_body]
    - [idg, bg, tg, gdef] is a block from the definition

    ...
    with idg bg : tg :=
      gdef
    ...

    - [fids] is the list [f1 ... fn] of identifiers of the mutual
    inductive blocks
    - [fbl] is the list of local binders [f1 ... fn]
    - [greps] is the list [(g1, g1_) ... (gk, gk_)] of nested blocks
      on which the block [idg] depends
    - [newid] is the new name for the generalized definition

    This function defines the following function :

    Definition newid f1 ... fn :=
      fix newid bg : tg :=
        let g1 := g1_ f1 ... fn in
        ...
        let gk := gk_ f1 ... fn in
        gdef [idg -> newid]
*)
let abstract_body fids fbl greps (idg, bg, tg, gdef) newid =
  let gdef_renamed =
    replace_vars_constr_expr [idg, newid] gdef in
  let gdef_with_lets =
    List.fold_left (fun constr (gid, gnewid) ->
		      CLetIn (Loc.ghost,
			      dl (Names.Name gid),
			      mkAppC (mkIdentC gnewid, fids),
			      constr)) gdef_renamed greps in
  let gfix =
    CFix (Loc.ghost, dl newid,
	  [dl newid, (None, CStructRec),
	   List.map mk_binder bg,
	   tg, gdef_with_lets]) in
  let g_ =
    abstract_constr_expr gfix fbl in
    declare_definition newid
      (Decl_kinds.Global, Decl_kinds.Definition)
      [] None g_ None (fun _ _ -> ())


(* Creates the generalized [g_] functions for all the
   [g] blocks on nested inductives. *)
let rec create_abstract_nested_bodies fids fbl greps = function
  | [] -> greps
  | ((idg, bg, tg, _) as body)::bodies ->
      let newid = add_suffix idg "_" in
	abstract_body fids fbl greps body newid;
	create_abstract_nested_bodies fids fbl ((idg, newid)::greps) bodies

(* [create_mutual_fixpoint]
   - [fids] is the list [f1 ... fn] of identifiers of the mutual
   inductive blocks
   - [greps] is the list [(g1, g1_) ... (gk, gk_)] of nested blocks
   idss and their new names, which should be substituted in the definition
   - [fdefs] is the list of mutually inductive blocks from the definition
   Nested Fixpoint f1 bl1 : t1 :=
     tf1
   with f2 bl2 : t2 :=
     tf2
   ...
   with fn bln : tn :=
     tfn
   end.

   The function defines the following fixpoint :
   Fixpoint f1 bl1 : t1 :=
     let g1 := g1_ f1 ... fn in ... let gk := gk_ f1 ... fn in
     tf1
   ...
   with fn bln : tn :=
     let g1 := g1_ f1 ... fn in ... let gk := gk_ f1 ... fn in
     tfn
   end.
*)
let create_mutual_fixpoint fids greps fdefs =
  let create_fixpoint_expr (idf, bf, tf, f) =
    let f_with_lets =
      List.fold_left (fun constr (gid, gnewid) ->
			CLetIn (Loc.ghost,
				dl (Names.Name gid),
				mkAppC (mkIdentC gnewid, fids),
				constr)) f greps
    in
      if_verbose msgnl (Ppconstr.pr_constr_expr f_with_lets);
      (dl idf, (None, CStructRec),
       List.map mk_binder bf,
       tf, Some f_with_lets)
  in
    Command.do_fixpoint
      (List.map (fun fdef -> create_fixpoint_expr fdef, []) fdefs)

(* Creates aliases for the nested blocks :
   Definition g1 := g1_ f1 ... fn.
   ...
   Definition gk := gk_ f1 ... fn.
*)
let create_aliases fids greps =
  List.iter (fun (gid, gnewid) ->
	       let galias = mkAppC (mkIdentC gnewid, fids) in
		 declare_definition gid
		   (Decl_kinds.Global, Decl_kinds.Definition)
		   [] None galias None (fun _ _ -> ())
	    ) greps

(* Takes a list of blocks and defines everything.
   Assumes the first n blocks correspond to a mutually inductive
   definition with n types, and the next blocks deal
   with nested inductives in topological order :

   Nested Fixpoint f1 (_ : I1) : T1 :=
   ...
   with f2 (_ : I2) : T2 :=
   ...
   with fn (_ : In) : Tn :=
   ...
   with g1 (_ : J1(I1, ..., In)) : S1 :=
   ...
   with gk (_ : Jk(I1, ..., In)) : Sk :=
   ...
   end.

   (gi depends on gj, j < i)
*)
let nested_fixpoint bodyl =
  match bodyl with
    | (_, bl, _, _)::_ ->
	begin
	  match bl with
	    | (_, c)::_ ->
		let constr =
		  Constrintern.interp_constr Evd.empty (Global.env ()) c in
		let (ind, _) = Inductive.find_rectype (Global.env ()) constr in
		let (mind, _) = Global.lookup_inductive ind in
		let n = mind.Declarations.mind_ntypes in
		let mbodyl, nbodyl = split_at n bodyl in
		  if_verbose msgnl (str "Mutual definitions :");
		  List.iter (fun def ->
			       if_verbose msgnl (pr_nfix_definition def)) mbodyl;
		  if_verbose msgnl (str "Nested definitions :");
		  List.iter (fun def ->
			       if_verbose msgnl (pr_nfix_definition def)) nbodyl;
		  (* f1 with f2 ... with fn with g1 with .... with gk *)
		  let fids =
		    List.map (fun (id, _, _, _) -> mkIdentC id) mbodyl in
		  let fbl : local_binder list =
		    List.map (fun (id, bl, t, _) ->
				let rt = mkCProdN Loc.ghost
				  (List.map mk_binder bl) t in
				  mk_binder ([id], rt))
		      mbodyl
		  in
		  let greps =
		    create_abstract_nested_bodies fids fbl [] nbodyl
		  in
		    create_mutual_fixpoint fids greps mbodyl;
		    create_aliases fids greps
	    | [] -> if_verbose msgnl (str "Empty list of binders")
	end
    | [] -> if_verbose msgnl (str "Empty list of definitions")

VERNAC COMMAND EXTEND NestedFixpoint
  [ "Nested" "Fixpoint"
      ne_nfix_definition_list_sep(bodyl,"with")
  ] ->
    [
      nested_fixpoint bodyl
    ]
END
