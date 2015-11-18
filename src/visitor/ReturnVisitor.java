package visitor;

import ast.AssertStmt;
import ast.CandidatePostcondition;
import ast.Expr;
import ast.Node;
import ast.NumberExpr;
import ast.Postcondition;
import ast.ProcedureDecl;
import ast.Stmt;
import ast.TraceableNode.SourceType;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import tool.CandidateAssertCollector;
import tool.SMTUtil;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Visitor used to transform postconditions using the result from the return statement to asserts
 * put at the end.
 */
public class ReturnVisitor extends DefaultVisitor {
    private final CandidateAssertCollector candidateAssertCollector;

    public ReturnVisitor(CandidateAssertCollector candidateAssertCollector) {
        sourceType = SourceType.RETURN;
        this.candidateAssertCollector = candidateAssertCollector;
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        List<Stmt> stmts = procedureDecl.getStmts();
        stmts.addAll(
            createPostconditionAsserts(
                procedureDecl.getPostconditions(),
                procedureDecl.getCandidatePostconditions(),
                procedureDecl.getReturnExpr()));
        return new ProcedureDecl(
            procedureDecl.getName(),
            procedureDecl.getParams(),
            procedureDecl.getConditions(),
            stmts,
            new NumberExpr("not needed anymore"));
    }

    @Override
    public String getDescription() {
        return "Return visitor";
    }

    public List<AssertStmt> createPostconditionAsserts(
        List<Postcondition> postconditions,
        List<CandidatePostcondition> candidatePostconditions,
        Expr returnExpr) {
        Map<String, Expr> substitutes = Maps.newHashMap();
        substitutes.put(SMTUtil.RESULT_PLACEHOLDER, returnExpr);

        List<AssertStmt> postAsserts = postconditions.stream()
            .map(p -> new AssertStmt(p.getCondition().replace(substitutes), null))
            .collect(Collectors.toList());
        List<AssertStmt> candidatePostAsserts = candidatePostconditions.stream()
            .map(post -> {
                AssertStmt assertStmt = new AssertStmt(post.getCondition().replace(substitutes), null);
                candidateAssertCollector.add(post, assertStmt);
                return assertStmt;
            }).collect(Collectors.toList());

        List<AssertStmt> result = Lists.newArrayList(postAsserts);
        result.addAll(candidatePostAsserts);

        return result;
    }
}
