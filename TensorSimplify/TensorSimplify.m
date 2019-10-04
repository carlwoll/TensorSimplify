(* Wolfram Language Package *)

(* Created by the Wolfram Workbench Sep 10, 2017 *)

BeginPackage["TensorSimplify`"]

FromTensor::usage = "FromTensor[tensor] attempts to convert the tensor to an equivalent form using Dot and Tr"
ToTensor::usage = "ToTensor[dot] attempts to convert a dot product into a  tensor"
TensorSimplify::usage = "TensorSimplify attempts to reduce tensors taking into account properties of Dot, Tr and simplifying symbolic identity tensors where possible"
IdentityReduce::usage = "IdentityReduce eliminates contracted identity tensors"

TensorSimplify::unkrnk = "Unable to determine tensor rank of `1`"

Begin["`Private`"]

Options[TensorSimplify] = {Assumptions :> $Assumptions, "Tensors"->Automatic};

TensorSimplify[expr_, OptionsPattern[]] := Module[{output = Replace[OptionValue["Tensors"], Except[_?BooleanQ] :> FreeQ[expr, Dot|Tr]], res},
	Block[{$Assumptions = OptionValue[Assumptions]},
		res = IdentityReduce @ TensorReduce[ToTensor @ expr];
		res = res /. t:(TensorTranspose | TensorContract) :> TensorReduce @* t;
		If[TrueQ@output,
			res,
			FromTensor @ res
		]
	]
]

ToTensor[expr_] := expr /. {Dot->dot, Tr->tr}

dot[a__] := Replace[SymbolicTensors`DotToTensorContract[Dot[a]], _SymbolicTensors`DotToTensorContract -> Dot[a]]

tr[a_] /; TensorRank[a] == 2 := TensorContract[a, {{1, 2}}]
tr[a_, Plus, 2] := TensorContract[a, {{1, 2}}]
tr[a___] := Tr[a]



FromTensor[expr_] := expr /. TensorContract->tc

tc[a_TensorProduct, i_] := Module[{res = itc[a, i]},
	res /; res =!= $Failed]

tc[a_, {{1, 2}}] /; TensorRank[a] == 2 := Tr[Replace[a, (Transpose|TensorTranspose)[m_, {2, 1} | PatternSequence[]]-> m]]

tc[a__] := TensorContract[a]

itc[a_TensorProduct, i_] := Module[
	{indices, rnk, s=0, ends, g, nodes, info, tlist, res},
	indices = Quiet@tensorIndices[a];
	rnk=TensorRank @ TensorContract[a,i];

	(* 
	 * Determine ends of the contraction chain.
	 * For Tr, remove one set of indices, and find contraction 
	 * chain of remaining indices
	 *)

	ends = Switch[{rnk, Sort@Tally[Length/@indices]},
		{0, {{2,_}}}, Complement[Range@TensorRank[a], Flatten@Most@i],
		{2, {{2,_}}}, Complement[Range@TensorRank[a],Flatten@i],
		{1, {{1,1},{2,_}}}, {0, First@Complement[Range@TensorRank[a],Flatten@i]},
		{0, {{1,2},{2,_}|PatternSequence[]}}, {0,-1},
		_,Return[$Failed]
	];

	(* find contraction chain. Augment vectors with 0 | -1 so that each node is a pair *)
	g = FindPath[
		Graph @ Join[
			Cases[indices, p:{_,_} :> UndirectedEdge@@p],
			Cases[indices,{p_} :> UndirectedEdge[s--, p]],
			UndirectedEdge @@@ i
		],
		First@ends,
		Last@ends,
		{2 (Length[i] - Boole[rnk == 0 && Min[ends]>0])+ 1}
	];
	(* unable to find a single contraction containing all tensors *)
	If[g === {}, Return[$Failed, Module]];

	(* find node (tensor) indices in the contraction chain *)
	nodes = DeleteCases[Partition[First@g, 2, 2], 0|-1, Infinity];

	(* determine tensors corresponding to indices, and whether to transpose tensor *)
	info=Table[
		Query[Select[MemberQ[n]], MatchQ[{n,___}]][indices],
		{n, nodes[[All,1]]}
	];

	(* standardize Transpose *)
	tlist = Replace[
		List@@a,
		(TensorTranspose | Transpose)[m_, {2, 1}] -> Transpose[m],
		{1}
	]; 

	(* create equivalent Dot product *)
	res = Dot @@ MapThread[
		If[#2, #1, Transpose[#1]]&,
		{
			tlist[[Flatten@Keys[info]]],
			Flatten@Values[info]
		}
	];
	res = Replace[res, Transpose[Transpose[m_]] :> m, {1}];

	(* For 0-rank outputs, determine whether the normal or "transposed" version has fewer Transpose's *)
	Which[
		rnk > 0,
		res,

		TensorRank[res] > 0,
		If[Count[res, _Transpose] > Length[a]/2,
			Tr @ Replace[Reverse[res], {Transpose[m_]:>m, m_:>Transpose[m]}, {1}],
			Tr @ res
		],

		Count[res,_Transpose] > Length[a]/2-1,
		res = List @@ Reverse[res];
		res[[2 ;; -2]] = Replace[res[[2 ;; -2]], {Transpose[m_]:>m, m_:>Transpose[m]}, {1}];
		Dot @@ res,

		True,
		res
	]
]

(* tensorIndices returns a list of node -> indices rules *)
tensorIndices[Verbatim[TensorProduct][t__]] := With[{r=Accumulate @* Map[TensorRank] @ {1,t}},
	If[MatchQ[r, {__Integer}],
		Association @ Thread @ Rule[
			Range@Length[{t}], 
			Range[1+Most[r], Rest[r]]
		],
		Message[TensorSimplify::unkrnk, {t}[[Position[r, Except[_Integer], 1, 1][[1,1]]-1]]]
	]
]



IdentityReduce[e_] := e /. TensorContract->ir

ir[t_TensorProduct, i_] := Module[{indices, imIndices, ids, dummy},
	indices = tensorIndices[t];
	If[indices === $Failed, Return[TensorContract[t, i]]];
	imIndices = Position[
		Replace[t, Inactive[IdentityMatrix][n_] -> dummy[n], {1}],
		IdentityMatrix | dummy,
		{2}
	];
	ids = Pick[
		imIndices,
		IntersectingQ[Flatten[i],indices[#]]& /@ imIndices[[All,1]]
	];
	If[ids==={},
		TensorContract[t,i],
		TensorContract[ReplacePart[t, ids[[1]]->SymbolicTensors`IdentityTensor],i] /. TensorContract->ir
	]
]

ir[(Inactive[IdentityMatrix] | IdentityMatrix)[n_], {{1,2}}]=n;
ir[o_, i_]:=TensorContract[o,i]

End[]

EndPackage[]

