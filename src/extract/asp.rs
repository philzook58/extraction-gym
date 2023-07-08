use super::*;
use clingo::control;

use clingo::ClingoError;
use clingo::FactBase;
use clingo::ShowType;
use clingo::Symbol;
use clingo::ToSymbol;

// An enode is identified with the eclass id and then index in that eclasses enode list.
#[derive(ToSymbol)]
struct Enode {
    eid: u32,
    node_i: u32,
    op: String,
    cost: i32,
}

#[derive(ToSymbol)]
struct BottomSel {
    eid: u32,
    node_i: u32,
}

#[derive(ToSymbol)]
struct Root {
    eid: u32,
}

#[derive(ToSymbol)]
struct Child {
    eid: u32,
    node_i: u32,
    child_eid: u32,
}

const ASP_PROGRAM: &str = "
eclass(E) :- enode(E,_,_,_).

% we may choose to select this enode if we have selected that class of all it's children.
{ sel(E,I) } :- enode(E,I,_,_), selclass(Ec) : child(E,I,Ec).

% if we select an enode in an eclass, we select that eclass
selclass(E) :- sel(E,_).

% It is inconsistent for a eclass to be a root and not selected.
% This is *not* the same as saying  selclass(E) :- root(E). 
:- root(E), not selclass(E).

% As a redundant constraint, each eclass should have at most one enode selected
:- eclass(E), #count { E,I : sel(E,I)} > 1.

% The actual cost function
#minimize { C@4,E,I : sel(E,I), enode(E,I,_,C) }.

% heuristically make choices tree cost model would
treecost(E,C1) :- eclass(E), C1 = #min { C,E,I : treecost(E,I,C) }.
treecost(E,I,C1 + Cs) :- enode(E,I,_,C1), Cs = #sum { C, Ec : child(E,I,Ec), treecost(Ec,C) }, Cs < 20.
treesel(E,I) :- treecost(E,I,C), treecost(E,C). 


treemax(E,C1) :- eclass(E), C1 = #max { C,E,I : treecost(E,I,C) }.
treenorm(E,I,(C - Cmin)/(Cmax - Cmin + 1)) :- treecost(E,Cmin), treemax(E,Cmax), treecost(E,I,C).

#maximize {1@3,E : treesel(E,I), sel(E,I)}.
%#maximize { C@3,E : treenorm(E,I,C), sel(E,I)}.

#minimize { 1@2,E : sel(E,I) }. % minimizing number of eclasses is a decent heuristic

#minimize { E*I@1,E,I : sel(E,I) }. % symmetry break to just prefer lower I?

#show sel/2.
";

pub struct AspExtractor;
impl Extractor for AspExtractor {
    fn extract(&self, egraph: &SimpleEGraph, _roots: &[Id]) -> ExtractionResult {
        let mut ctl = control(vec![]).expect("REASON");

        let mut fb = FactBase::new();
        for eid in egraph.roots.iter() {
            let root = Root {
                eid: (*eid).try_into().unwrap(),
            };

            //println!("{}.", root.symbol().expect("should be symbol"));
            fb.insert(&root);
        }
        /*
        let bottom_result = bottom_up::BottomUpExtractor.extract(egraph, _roots);
        for (eid, node_i) in bottom_result.choices.iter().enumerate() {
            let bottomsel = BottomSel {
                eid: eid.try_into().unwrap(),
                node_i: (*node_i).try_into().unwrap(),
            };
            fb.insert(&bottomsel);
        } */
        for (_i, class) in egraph.classes.values().enumerate() {
            for (node_i, node) in class.nodes.iter().enumerate() {
                let enode = Enode {
                    eid: class.id.try_into().unwrap(),
                    node_i: node_i.try_into().unwrap(),
                    op: node.op.clone(),
                    cost: node.cost.round() as i32,
                };
                //println!("{}.", enode.symbol().expect("should be symbol"));
                fb.insert(&enode);
                for child_eid in node.children.iter() {
                    let child = Child {
                        eid: class.id.try_into().unwrap(),
                        node_i: node_i.try_into().unwrap(),
                        child_eid: (*child_eid).try_into().unwrap(),
                    };
                    //println!("{}.", child.symbol().expect("should be symbol"));
                    fb.insert(&child);
                }
            }
        }

        ctl.add_facts(&fb).expect("Failed to add factbase");

        ctl.add("base", &[], ASP_PROGRAM)
            .expect("Failed to add a logic program.");
        let part = clingo::Part::new("base", vec![]).unwrap();
        let parts = vec![part];
        ctl.ground(&parts).expect("Failed to ground");
        let mut handle = ctl
            .solve(clingo::SolveMode::YIELD, &[]) // stl.optimal_models()
            .expect("Failed to solve");
        let mut result = ExtractionResult::new(egraph.classes.len());
        let mut ran_once = false;
        let start_time = std::time::Instant::now();
        while let Some(model) = handle.model().expect("model failed") {
            ran_once = true;
            let atoms = model
                .symbols(ShowType::SHOWN)
                .expect("Failed to retrieve symbols in the model.");
            //println!("atoms length {}", atoms.len());
            for symbol in atoms {
                assert!(symbol.name().unwrap() == "sel");
                let args = symbol.arguments().unwrap();
                result.choices[args[0].number().unwrap() as usize] =
                    args[1].number().unwrap() as usize;
                //println!("{}", symbol);
            }

            //if !handle.wait(Duration::from_secs(30)) {
            //    break;
            //}
            let elapsed = start_time.elapsed();
            if elapsed.as_secs() > 15 {
                log::info!("early stop asp");
                break;
            }
            handle.resume().expect("Failed resume on solve handle.");
        }
        //assert!(ran_once);

        handle.close().expect("Failed to close solve handle.");
        result
    }
}
