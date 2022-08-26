mkdir -p mvn/src/{main,test}/java

# use maven build scripts from test-generation-examples as template to compile to Java
dotnet dafny/Binaries/Dafny.dll /spillTargetCode:3 /compileTarget:java /out:pkgs /noVerify test/AllTests.dfy

java_test_file="pkgs.java"
java_dir_name="pkgs-java"

mv $java_dir_name/$java_test_file mvn/src/test/java
for package in $(find $java_dir_name -mindepth 1 -maxdepth 1 -type d  -name '*UnitTests_Compile'); do
  mv $package mvn/src/test/java
done
for package in $(find $java_dir_name -mindepth 1 -maxdepth 1 -type d -print); do
    mv $package mvn/src/main/java
done

# main src files cannot refer to unit test files, so delete those import statements
for java_file in $(find mvn/src/main/java -name '*.java'); do
  sed -i '/UnitTests_Compile.*/d' $java_file
done

  mkdir mvn/lib
  cp $java_dir_name/DafnyRuntime.jar mvn/lib
  rm -rf $java_dir_name

  # generate pom.xml
  cat <<EOF | tee mvn/pom.xml >/dev/null
<project xmlns="http://maven.apache.org/POM/4.0.0" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 https://maven.apache.org/xsd/maven-4.0.0.xsd">
  <modelVersion>4.0.0</modelVersion>

  <groupId>libraries</groupId>
  <artifactId>byu-libraries</artifactId>
  <version>1.0.0</version>

  <name>byu-libraries</name>
  <description>standard library</description>

  <properties>
    <project.build.sourceEncoding>UTF-8</project.build.sourceEncoding>
  </properties>

  <dependencyManagement>
    <dependencies>
      <dependency>
        <groupId>org.junit</groupId>
        <artifactId>junit-bom</artifactId>
        <version>5.7.2</version>
        <type>pom</type>
        <scope>import</scope>
      </dependency>
    </dependencies>
  </dependencyManagement>

  <dependencies>
    <dependency>
      <groupId>dafny.lang.runtime</groupId>
      <artifactId>DafnyRuntime</artifactId>
      <version>14.0</version>
      <scope>system</scope>
      <!-- Change system path to match your directory-->
      <systemPath>$HOME/libraries/mvn/lib/DafnyRuntime.jar</systemPath>
    </dependency>
    <dependency>
      <groupId>org.junit.jupiter</groupId>
      <artifactId>junit-jupiter</artifactId>
      <scope>test</scope>
    </dependency>
    <dependency>
      <groupId>org.junit.platform</groupId>
      <artifactId>junit-platform-console-standalone</artifactId>
      <version>1.7.2</version>
    </dependency>
    <dependency>
      <groupId>org.mockito</groupId>
      <artifactId>mockito-core</artifactId>
      <version>4.0.0</version>
    </dependency>
    <dependency>
      <groupId>org.mockito</groupId>
      <artifactId>mockito-junit-jupiter</artifactId>
      <version>4.0.0</version>
      <scope>test</scope>
    </dependency>
  </dependencies>

  <build>
    <plugins>
      <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-compiler-plugin</artifactId>
        <version>3.6.0</version>
        <configuration>
          <source>11</source>
          <target>11</target>
        </configuration>
      </plugin>
      <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-surefire-plugin</artifactId>
        <version>3.0.0-M5</version>
        <configuration>
          <includes>
            <include>**/*.java</include>
          </includes>
        </configuration>
      </plugin>
      <plugin>
        <groupId>org.jacoco</groupId>
        <artifactId>jacoco-maven-plugin</artifactId>
        <version>0.8.7</version>
        <executions>
          <execution>
            <goals>
              <goal>prepare-agent</goal>
            </goals>
          </execution>
          <execution>
            <id>report</id>
            <phase>prepare-package</phase>
            <goals>
              <goal>report</goal>
            </goals>
          </execution>
        </executions>
      </plugin>
    </plugins>
  </build>
</project>
EOF

  # run test suite with mvn clean test, generate report
  mvn -f mvn clean test jacoco:report