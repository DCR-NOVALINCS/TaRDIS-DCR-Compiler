package app;

import pt.unl.fct.di.novasys.babel.exceptions.HandlerRegistrationException;

import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import dcr.*;
import dcr.Relation.RelationType;
import dcr.ast.typing.*;
import dcr.ast.*;
import dcr.ast.ASTRecord.RecordField;

public class App extends DCRProtocol {

  public static final short PROTO_ID = 2; // unique protocol id

  public App() {
    super("DcrApp", PROTO_ID);
  }

  @Override
  public void init(Properties properties) throws HandlerRegistrationException, IOException {
    try {
      super.init(properties);

      String name = properties.getProperty("target-name");

// {{code}}

      readSystemIn();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  private static final ASTNode eventValueFieldAsASTNode(String eventId) {
    return new ASTDeref(
        new ASTRecordField("value", new ASTId(eventId)));
  }

  private static final <T> Set<T> newHashSet(T... objs) {
    Set<T> set = new HashSet<T>();
    Collections.addAll(set, objs);
    return set;
  }
}
