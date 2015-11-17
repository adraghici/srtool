package visitor;

import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.LoopInvariant;
import ast.Node;
import ast.PrePostCondition;
import ast.ProcedureDecl;
import ast.WhileStmt;
import com.google.common.collect.Lists;

import java.util.List;
import java.util.stream.Collectors;

public class RemovingVisitor extends DefaultVisitor {
    private final List<Node> removalCandidates;

    public RemovingVisitor(List<Node> removalCandidates) {
        this.removalCandidates = removalCandidates;
    }

    @Override public Object visit(ProcedureDecl procedureDecl) {
        List<CandidatePrecondition> remainingCandidatePreconditions =
            procedureDecl.getCandidatePreconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .collect(Collectors.toList());
        List<CandidatePostcondition> remainingCandidatePostconditions =
            procedureDecl.getCandidatePostconditions().stream()
                .filter(p -> !removalCandidates.contains(p))
                .collect(Collectors.toList());

        List<PrePostCondition> conditions = Lists.newArrayList();
        conditions.addAll(procedureDecl.getPreconditions());
        conditions.addAll(remainingCandidatePreconditions);
        conditions.addAll(procedureDecl.getPostconditions());
        conditions.addAll(remainingCandidatePostconditions);

        return new ProcedureDecl(
            procedureDecl.getName(),
            procedureDecl.getParams(),
            conditions,
            procedureDecl.getStmts(),
            procedureDecl.getReturnExpr());
    }

    @Override public Object visit(WhileStmt whileStmt) {
        List<CandidateInvariant> remainingCandidateInvariants =
            whileStmt.getCandidateInvariants().stream()
                .filter(i -> !removalCandidates.contains(i))
                .collect(Collectors.toList());

        List<LoopInvariant> invariants = Lists.newArrayList();
        invariants.addAll(whileStmt.getInvariants());
        invariants.addAll(remainingCandidateInvariants);

        return new WhileStmt(whileStmt.getCondition(), whileStmt.getWhileBlock(), invariants);
    }
}
