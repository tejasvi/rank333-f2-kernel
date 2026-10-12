module
public import R22Port.U_d41d8cd98f00
public import R22N.Glue
/-! # KB.AggT: the Cov closure over keys alone, for scale tests of the aggregators (no item data)

`KB.CovOfKeyT k` is `R22N.Cov (fun _ => True) (interface of k)`: the same closure as the case-(II) aggregators prove, with a trivial
checked predicate, so the aggregator's own kernel work (decoding keys, matching each child with its parent's ext / rng entry,
the `AllL` chains and projections) can be measured on a real store's keys without item modules. -/
@[expose] public section
namespace KB

/-- the scale test's per-key statement -/
def CovOfKeyT (k : Nat) : Prop := R22N.Cov (fun _ => True) ((R22N.SegI.ofKey k).root, (R22N.SegI.ofKey k).lo)

end KB
