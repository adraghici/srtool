package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.BinaryExpr;
import ast.BlockStmt;
import ast.CallStmt;
import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.Expr;
import ast.HavocStmt;
import ast.IfStmt;
import ast.Invariant;
import ast.LoopInvariant;
import ast.NumberExpr;
import ast.OldExpr;
import ast.ParenExpr;
import ast.Postcondition;
import ast.PrePostCondition;
import ast.Precondition;
import ast.ProcedureDecl;
import ast.ProcedureRef;
import ast.Program;
import ast.ResultExpr;
import ast.Stmt;
import ast.TernaryExpr;
import ast.UnaryExpr;
import ast.VarDeclStmt;
import ast.VarRef;
import ast.VarRefExpr;
import ast.WhileStmt;
import com.google.common.collect.Lists;
import tool.NodeCollector;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to traverse the whole AST and return a new copy of it.
 */
public class DefaultVisitor implements Visitor<Object> {
    protected final NodeCollector nodeCollector;

    public DefaultVisitor() {
        nodeCollector = new NodeCollector();
    }

    public DefaultVisitor(NodeCollector nodeCollector) {
        this.nodeCollector = nodeCollector;
    }

    @Override
    public Object visit(Program program) {
        List<VarDeclStmt> varDeclStmts =
            program.getGlobalDecls().stream()
                .map(g -> (VarDeclStmt) g.accept(this))
                .collect(Collectors.toList());
        List<ProcedureDecl> procedureDecls =
            program.getProcedureDecls().stream()
                .map(p -> (ProcedureDecl) p.accept(this))
                .collect(Collectors.toList());
        return new Program(varDeclStmts, procedureDecls);
    }

    @Override
    public Object visit(VarDeclStmt varDeclStmt) {
        return new VarDeclStmt((VarRef) varDeclStmt.getVarRef().accept(this));
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        List<VarRef> params = procedureDecl.getParams().stream()
            .map(p -> (VarRef) p.accept(this))
            .collect(Collectors.toList());
        List<PrePostCondition> conditions = procedureDecl.getConditions().stream()
            .map(p -> (PrePostCondition) p.accept(this))
            .collect(Collectors.toList());
        List<Stmt> stmts = procedureDecl.getStmts().stream()
            .map(v -> (Stmt) v.accept(this))
            .collect(Collectors.toList());
        Expr returnExpr = (Expr) procedureDecl.getReturnExpr().accept(this);
        return new ProcedureDecl(procedureDecl.getName(), params, conditions, stmts, returnExpr);
    }

    @Override
    public Object visit(Precondition precondition) {
        Precondition pre = new Precondition((Expr) precondition.getCondition().accept(this));
        nodeCollector.add(precondition, pre);
        return pre;
    }

    @Override
    public Object visit(Postcondition postcondition) {
        Postcondition post = new Postcondition((Expr) postcondition.getCondition().accept(this));
        nodeCollector.add(postcondition, post);
        return post;
    }

    @Override
    public Object visit(CandidatePrecondition candidatePrecondition) {
        return new CandidatePrecondition(
            (Expr) candidatePrecondition.getCondition().accept(this));
    }

    @Override
    public Object visit(CandidatePostcondition candidatePostcondition) {
        return new CandidatePostcondition(
            (Expr) candidatePostcondition.getCondition().accept(this));
    }

    @Override
    public Object visit(AssignStmt assignStmt) {
        VarRef varRef = (VarRef) assignStmt.getVarRef().accept(this);
        Expr expr = (Expr) assignStmt.getExpr().accept(this);
        return new AssignStmt(varRef, expr);
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        AssertStmt stmt = new AssertStmt((Expr) assertStmt.getCondition().accept(this));
        nodeCollector.add(assertStmt, stmt);
        return stmt;
    }

    @Override
    public Object visit(AssumeStmt assumeStmt) {
        return new AssumeStmt((Expr) assumeStmt.getCondition().accept(this));
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        return new HavocStmt((VarRef) havocStmt.getVarRef().accept(this));
    }

    @Override
    public Object visit(CallStmt callStmt) {
        List<Expr> args = callStmt.getArgs().stream()
            .map(e -> (Expr) e.accept(this))
            .collect(Collectors.toList());
        VarRef varRef = (VarRef) callStmt.getVarRef().accept(this);
        ProcedureRef procedureRef = (ProcedureRef) callStmt.getProcedureRef().accept(this);
        return new CallStmt(varRef, procedureRef, args);
    }

    @Override
    public Object visit(IfStmt ifStmt) {
        Expr condition = (Expr) ifStmt.getCondition().accept(this);
        BlockStmt thenBlock = (BlockStmt) ifStmt.getThenBlock().accept(this);
        Optional<BlockStmt> elseBlock = ifStmt.getElseBlock();
        Optional<BlockStmt> optionalElseBlock = elseBlock.isPresent()
            ? Optional.of((BlockStmt) elseBlock.get().accept(this))
            : Optional.empty();
        return new IfStmt(condition, thenBlock, optionalElseBlock);
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        BlockStmt whileBlock = (BlockStmt) whileStmt.getWhileBlock().accept(this);
        List<LoopInvariant> invariants = whileStmt.getLoopInvariants().stream()
            .map(i -> (LoopInvariant) i.accept(this))
            .collect(Collectors.toList());
        WhileStmt loop = new WhileStmt(condition, whileBlock, invariants);
        nodeCollector.add(whileStmt, loop);
        return loop;
    }

    @Override
    public Object visit(BlockStmt blockStmt) {
        List<Stmt> stmts = blockStmt.getStmts().stream()
            .map(s -> (Stmt) s.accept(this))
            .collect(Collectors.toList());
        return new BlockStmt(stmts);
    }

    @Override
    public Object visit(Invariant invariant) {
        Invariant inv = new Invariant((Expr) invariant.getCondition().accept(this));
        nodeCollector.add(invariant, inv);
        return inv;
    }

    @Override
    public Object visit(CandidateInvariant candidateInvariant) {
        return new CandidateInvariant((Expr) candidateInvariant.getCondition().accept(this));
    }

    @Override
    public Object visit(VarRef varRef) {
        return new VarRef(varRef.getVar());
    }

    @Override
    public Object visit(TernaryExpr ternaryExpr) {
        Expr condition = (Expr) ternaryExpr.getCondition().accept(this);
        Expr trueExpr = (Expr) ternaryExpr.getTrueExpr().accept(this);
        Expr falseExpr = (Expr) ternaryExpr.getFalseExpr().accept(this);
        return new TernaryExpr(condition, trueExpr, falseExpr);
    }

    @Override
    public Object visit(BinaryExpr binaryExpr) {
        Expr left = (Expr) binaryExpr.getLeft().accept(this);
        Expr right = (Expr) binaryExpr.getRight().accept(this);
        return new BinaryExpr(binaryExpr.getOperator(), left, right);
    }

    @Override
    public Object visit(UnaryExpr unaryExpr) {
        Expr atom = (Expr) unaryExpr.getAtom().accept(this);
        return new UnaryExpr(atom, Lists.newArrayList(unaryExpr.getOperators()));
    }

    @Override
    public Object visit(NumberExpr numberExpr) {
        return new NumberExpr(numberExpr.getNumber());
    }

    @Override
    public Object visit(VarRefExpr varRefExpr) {
        return new VarRefExpr((VarRef) varRefExpr.getVarRef().accept(this));
    }

    @Override
    public Object visit(ParenExpr parenExpr) {
        return new ParenExpr((Expr) parenExpr.getExpr().accept(this));
    }

    @Override
    public Object visit(ResultExpr resultExpr) {
        return new ResultExpr(resultExpr.getToken());
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        return new OldExpr((VarRef) oldExpr.getVarRef().accept(this));
    }

    @Override
    public Object visit(ProcedureRef procedureRef) {
        return new ProcedureRef(procedureRef.getName());
    }

    @Override public String getDescription() {
        return "";
    }
}
