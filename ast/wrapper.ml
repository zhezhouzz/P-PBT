type p_wrapper =
  | WrapperEnum of { enum_name : string; elems : string list }
  | WrapperTypeAlias of { type_name : string; alias_type : Nt.t }
  | WrapperEventDecl of { event_name : string; event_type : Nt.t }
  | WrapperMachineDecl of { machine_name : string; machine_type : Nt.t }
  | WrapperSpecEventDecl of {
      event_name : string;
      spec_event_type : Nt.t;
      p_event_name : string;
      p_event_type : Nt.t option;
    }
  | Dummy

let mk_spec_event_decl (event_name, p_event_name) spec_event_type =
  WrapperSpecEventDecl
    { event_name; spec_event_type; p_event_name; p_event_type = None }

let mk_machine_decl machine_name =
  WrapperMachineDecl
    { machine_name; machine_type = Nt.Ty_constructor ("machine", []) }
