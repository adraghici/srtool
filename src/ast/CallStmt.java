package ast;

import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class CallStmt implements Stmt {
    private final VarRef varRef;
    private final ProcedureRef procedureRef;
    private final List<Expr> args;

    public CallStmt(VarRef varRef, ProcedureRef procedureRef, List<Expr> args) {
        this.varRef = varRef;
        this.procedureRef = procedureRef;
        this.args = args;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    public ProcedureRef getProcedureRef() {
        return procedureRef;
    }

    public List<Expr> getArgs() {
        return args;
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(getVarRef().getVar());
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
