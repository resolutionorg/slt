import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Ch1
import Blueprint.Ch2
import Blueprint.Ch4
import Blueprint.Ch5
import Blueprint.Ch6
import Blueprint.Ch7
import Blueprint.Conventions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic Geometry and Statistical Learning Theory" =>

This document describes the Lean formalisation of the main theorems of {cite Wat09}[], Sumio
Watanabe's *Algebraic Geometry and Statistical Learning Theory*, in the library `slt`. The library
states the theorems under the *relatively finite variance* of {cite Wat18}[Definition 7] in place
of the book's realizability ({ref "conv-rfv"}[]). It is a reference: every statement it discusses
is a declaration, linked by name, and the boxes under a node record how the declaration's statement
relates to the book, as explained in {ref "conv-annotations"}[the appendix].

{include 0 Blueprint.Ch1}
{include 0 Blueprint.Ch2}
{include 0 Blueprint.Ch4}
{include 0 Blueprint.Ch5}
{include 0 Blueprint.Ch6}
{include 0 Blueprint.Ch7}
{include 0 Blueprint.Conventions}

{blueprint_graph}
{blueprint_summary}
{blueprint_bibliography}
