package ast;

import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class ProcedureDecl implements Node {
    private final String name;
    private final List<VarRef> params;
    private final List<PrePostCondition> conditions;
    private final List<Stmt> stmts;
    private final Expr returnExpr;

    public ProcedureDecl(String name, List<VarRef> params, List<PrePostCondition> conditions,
        List<Stmt> stmts, Expr returnExpr) {
        this.name = name;
        this.params = params;
        this.conditions = conditions;
        this.stmts = stmts;
        this.returnExpr = returnExpr;
    }

    public String getName() {
        return name;
    }

    public List<VarRef> getParams() {
        return params;
    }

    public List<PrePostCondition> getConditions() {
        return conditions;
    }

    public List<Precondition> getPreconditions() {
        return conditions.stream()
            .filter(x -> x instanceof Precondition)
            .map(x -> (Precondition) x)
            .collect(Collectors.toList());
    }

    public List<CandidatePrecondition> getCandidatePreconditions() {
        return conditions.stream()
            .filter(x -> x instanceof CandidatePrecondition)
            .map(x -> (CandidatePrecondition) x)
            .collect(Collectors.toList());
    }

    public List<Postcondition> getPostconditions() {
        return conditions.stream()
            .filter(x -> x instanceof Postcondition)
            .map(x -> (Postcondition) x)
            .collect(Collectors.toList());
    }

    public List<CandidatePostcondition> getCandidatePostconditions() {
        return conditions.stream()
            .filter(x -> x instanceof CandidatePostcondition)
            .map(x -> (CandidatePostcondition) x)
            .collect(Collectors.toList());
    }


    public List<Stmt> getStmts() {
        return stmts;
    }

    public Expr getReturnExpr() {
        return returnExpr;
    }

    @Override
    public Set<String> getModified() {
        return getStmts().stream()
            .map(Stmt::getModified)
            .flatMap(Set::stream)
            .collect(Collectors.toSet());
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
