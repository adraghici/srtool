package ast;

import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class WhileStmt implements Condition, Stmt {
    private final Expr condition;
    private final BlockStmt whileBlock;
    private final List<LoopInvariant> loopInvariants;

    public WhileStmt(Expr condition, BlockStmt whileBlock, List<LoopInvariant> loopInvariants) {
        this.condition = condition;
        this.whileBlock = whileBlock;
        this.loopInvariants = loopInvariants;
    }

    public List<LoopInvariant> getLoopInvariants() {
        return loopInvariants;
    }

    public List<Invariant> getInvariants() {
        return loopInvariants.stream()
            .filter(x -> x instanceof Invariant)
            .map(x -> (Invariant) x)
            .collect(Collectors.toList());
    }

    public List<CandidateInvariant> getCandidateInvariants() {
        return loopInvariants.stream()
            .filter(x -> x instanceof CandidateInvariant)
            .map(x -> (CandidateInvariant) x)
            .collect(Collectors.toList());
    }

    public BlockStmt getWhileBlock() {
        return whileBlock;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Set<String> getModified() {
        return getWhileBlock().getModified();
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
