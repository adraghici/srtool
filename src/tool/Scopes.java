package tool;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import java.util.ArrayList;
import java.util.List;

public class Scopes {
    private final IdMap idMap;
    private final List<Scope> scopes;

    /**
     * This will enter a default scope when created.
     */
    public Scopes() {
        idMap = new IdMap();
        scopes = new ArrayList<>();
        scopes.add(Scope.create(idMap));
    }

    public void enterScope() {
        scopes.add(Scope.fromScope(Iterables.getLast(scopes)));
    }

    public void enterScope(Scope scope) {
        scopes.add(scope);
    }

    public void exitScope() {
        scopes.remove(scopes.size() - 1);
    }

    public Scope globalScope() {
        return scopes.get(0);
    }

    public Scope topScope() {
        return Iterables.getLast(scopes);
    }

    public void declareVar(String var) {
        Iterables.getLast(scopes).declareVar(var);
    }

    public int getId(String var) {
        return Iterables.getLast(scopes).getId(var);
    }

    /**
     * Increases the id of the given variable from the fresh id provider and returns new id.
     */
    public int updateVar(String var) {
        int id = Iterables.getLast(scopes).increaseVar(var);
        Lists.reverse(scopes.subList(0, scopes.size() - 1)).stream()
            .filter(scope -> scope.hasVar(var))
            .forEach(scope -> scope.updateVar(var, id));
        return id;
    }
}
