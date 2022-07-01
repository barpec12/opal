package org.opalj.fpcf.fixtures.js;

import org.opalj.fpcf.properties.taint.ForwardFlowPath;

import javax.script.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

import static java.lang.Integer.parseInt;

public class Java2JsTestClass {
    private static int staticField;

    private int instanceField;

    @ForwardFlowPath({"simpleScriptEngineWithString"})
    public static void simpleScriptEngineWithString() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        try {
            se.eval("function check(str) {\n" +
                    "    return str === \"1337\";\n" +
                    "}");
        } catch (ScriptException e) {
            // never happens
        }
        String pw = source();

        Invocable inv = (Invocable) se;
        try {
            Boolean state = (Boolean) inv.invokeFunction("check", pw);
            sink(state);
        } catch (NoSuchMethodException e) {
            // never happens
        }
    }

    @ForwardFlowPath({"simpleScriptEngineWithFile"})
    public static void simpleScriptEngineWithFile() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        try {
            se.eval(new FileReader("check.js"));
        } catch (ScriptException e) {
            // never happens
        } catch (FileNotFoundException e) {
            // ignore
        }

        String pw = source();

        Invocable inv = (Invocable) se;
        try {
            Boolean state = (Boolean) inv.invokeFunction("check", pw);
            sink(state);
        } catch (NoSuchMethodException e) {
            // never happens
        }
    }

    @ForwardFlowPath({"simplePutGet"})
    public static void simplePutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");

        String pw = source();
        se.put("secret", pw);
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({"overapproxPutGet"})
    public static void overapproxPutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");

        String pw = source();
        // String is no constant
        se.put(Integer.toString(1337), pw);
        // TODO: Should we introduce a taint here or not?
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({})
    public static void overwritePutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");

        String pw = source();
        // String is no constant
        se.put("secret", pw);
        se.put("secret", "Const");
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({"bindingsSimplePutGet"})
    public static void bindingsSimplePutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        se.put("secret", pw);
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({"bindingsOverapproxPutGet"})
    public static void bindingsOverapproxPutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        // String is no constant
        se.put(Integer.toString(1337), pw);
        // TODO: Should we introduce a taint here or not?
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({})
    public static void BindingsOverwritePutGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        se.put("secret", pw);
        se.put("secret", "Const");
        Object out = se.get("secret");
        sink(out);
    }

    @ForwardFlowPath({})
    public static void bindingsPutRemoveGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        b.put("secret", pw);
        b.remove("secret");
        Object out = b.get("secret");
        sink(out);
    }

    @ForwardFlowPath({})
    public static void overwritePutRemoveGet() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        b.put("secret", pw);
        b.remove("secret");
        Object out = b.get("secret");
        sink(out);
    }

    @ForwardFlowPath({"bindingsPutAll"})
    public static void bindingsPutAll() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        Bindings b = se.createBindings();

        String pw = source();
        b.put("secret", pw);
        Bindings newb = se.createBindings();
        newb.putAll(b);
        Object out = newb.get("secret");
        sink(out);
    }

    public static String source() {
        return "1337";
    }

    private static int sanitize(int i) {return i;}

    private static void sink(int i) {
        System.out.println(i);
    }
    private static void sink(String i) {
        System.out.println(i);
    }
    private static void sink(boolean i) {
        System.out.println(i);
    }
    private static void sink(Object i) {
//        System.out.println(i);
    }
}
