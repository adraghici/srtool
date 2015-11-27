package visitor;

import ast.BinaryExpr;
import ast.BlockStmt;
import ast.CandidateInvariant;
import ast.Expr;
import ast.LoopInvariant;
import ast.NumberExpr;
import ast.ProcedureDecl;
import ast.VarRef;
import ast.VarRefExpr;
import ast.WhileStmt;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import ssa.Scopes;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visitor used to generate candidate invariants for Houdini.
 */
public class InvariantGenVisitor extends DefaultVisitor {
    private static final ImmutableList<String> COMPARISON_OPERATORS = ImmutableList.of("<=", "==");
    private static final ImmutableList<String> OPERATORS = ImmutableList.of("+", "-", "*");
    private static final ImmutableList<String> CONSTANTS = ImmutableList.of("0", "1", "2");

    private final Scopes scopes;
    private final Set<String> conditionVars;
    private final Set<NumberExpr> constants;

    public InvariantGenVisitor() {
        scopes = Scopes.withDefault();
        conditionVars = Sets.newHashSet();
        constants = Sets.newHashSet();
    }

    @Override
    public ProcedureDecl visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        ProcedureDecl result = (ProcedureDecl) super.visit(procedureDecl);
        scopes.exitScope();
        return result;
    }

    @Override
    public WhileStmt visit(WhileStmt whileStmt) {
        conditionVars.clear();
        constants.clear();

        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        List<LoopInvariant> loopInvariants = whileStmt.getLoopInvariants().stream().map(i -> (LoopInvariant) i.accept(this)).collect(Collectors.toList());

        Set<String> modsetVars = scopes.topScope().modset(whileStmt.getModified());
        Set<VarRef> vars = Sets.union(modsetVars, conditionVars).stream().map(VarRef::new).collect(Collectors.toSet());

        BlockStmt blockStmt = (BlockStmt) whileStmt.getWhileBlock().accept(this);

        constants.addAll(createDefaultConstants());
        loopInvariants.addAll(generateCandidateInvariants(vars));
        constants.clear();

        return new WhileStmt(condition, blockStmt, loopInvariants);
    }

    private List<CandidateInvariant> generateCandidateInvariants(Set<VarRef> vars) {
        List<VarRefExpr> varExprs = vars.stream().map(VarRefExpr::new).collect(Collectors.toList());
        List<Expr> conditions = Lists.newArrayList();

        // Expressions of the form: x <= 3.
        for (VarRefExpr varExpr : varExprs) {
            for (NumberExpr constant : constants) {
                for (String operator : COMPARISON_OPERATORS) {
                    conditions.add(new BinaryExpr(operator, varExpr, constant));
                }
            }
        }

        // Expressions of the form: x <= y.
        for (VarRefExpr left : varExprs) {
            for (VarRefExpr right : varExprs) {
                for (String operator : COMPARISON_OPERATORS) {
                    conditions.add(new BinaryExpr(operator, left, right));
                }
            }
        }

        // Expressions of the form: x * 2 == y;
        for (VarRefExpr left : varExprs) {
            for (VarRefExpr right : varExprs) {
                for (NumberExpr constant : constants) {
                    for (String op : OPERATORS) {
                        for (String comp : COMPARISON_OPERATORS) {
                            conditions.add(new BinaryExpr(comp, new BinaryExpr(op, left, constant), right));
                        }
                    }
                }
            }
        }

        return conditions.stream().map(CandidateInvariant::new).collect(Collectors.toList());
    }

    @Override
    public BlockStmt visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) super.visit(blockStmt);
        scopes.exitScope();
        return result;
    }

    @Override
    public VarRef visit(VarRef varRef) {
        conditionVars.add(varRef.getVar());
        scopes.topScope().updateVar(varRef.getVar(), 0);
        return varRef;

    }

    @Override
    public NumberExpr visit(NumberExpr numberExpr) {
        constants.add(numberExpr);
        return (NumberExpr) super.visit(numberExpr);
    }

    @Override
    public String getDescription() {
        return "Invariant generation visitor";
    }

    private static Set<NumberExpr> createDefaultConstants() {
        return CONSTANTS.stream().map(NumberExpr::new).collect(Collectors.toSet());
    }
}
