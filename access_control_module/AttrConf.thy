(*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *)

theory AttrConf
  imports Main
begin

locale AttrConf=
  fixes noelem::'element
    and noattr::'attr
    and noattrconf::"'attrconf"
    and attr_conf::"'attrconf\<Rightarrow>'attr\<Rightarrow>'attrconf"
    and is_attrconf::"'attrconf\<Rightarrow>bool"
    and attr_elem::"'attr\<Rightarrow>'element"
    and find_elem::"'attrconf\<Rightarrow>'attr\<Rightarrow>bool"
    and delete_attr::"'attrconf\<Rightarrow>'attr\<Rightarrow>'attrconf"
    and get_attr::"'attrconf\<Rightarrow>'element\<Rightarrow>'attr"
    and valid_attrconf::"'attrconf\<Rightarrow>bool"
  assumes ATTRCONFHLR1:"\<not>is_attrconf noattrconf"
  assumes ATTRCONFHLR2:"is_attrconf(attr_conf conf attr)"
  assumes ATTRCONFHLR3:"x=noattrconf\<or>(\<exists>conf attr. x=attr_conf conf attr)"
  assumes ATTRCONFHLR4:"attr_elem noattr=noelem"
  assumes ATTRCONFHLR6:"\<not>find_elem noattrconf attr"
  assumes ATTRCONFHLR7:"attr_elem attrx=attr_elem attr\<Longrightarrow>
                        find_elem(attr_conf conf attrx) attr"
  assumes ATTRCONFHLR8:"find_elem conf attr\<Longrightarrow>
                        find_elem(attr_conf conf attrx) attr"
  assumes ATTRCONFHLR9:"(\<not>find_elem conf attr)\<and>
                        attr_elem attrx\<noteq>attr_elem attr\<Longrightarrow>
                        \<not>find_elem(attr_conf conf attrx) attr"
  assumes ATTRCONFHLR10:"delete_attr noattrconf attr=noattrconf"
  assumes ATTRCONFHLR11:"attr_elem attrx=attr_elem attr\<Longrightarrow>
                        delete_attr(attr_conf conf attrx) attr=delete_attr conf attr"
  assumes ATTRCONFHLR12:"attr_elem attrx\<noteq>attr_elem attr\<Longrightarrow>
                        delete_attr(attr_conf conf attrx) attr=
                        attr_conf (delete_attr conf attr) attrx"
  assumes ATTRCONFHLR13:"get_attr noattrconf elem=noattr"
  assumes ATTRCONFHLR14:"attr_elem attr=elem\<Longrightarrow>
                        get_attr(attr_conf conf attr) elem=attr"
  assumes ATTRCONFHLR16:"attr_elem attr\<noteq>elem\<Longrightarrow>
                        get_attr(attr_conf conf attr) elem=get_attr conf elem"
  assumes ATTRCONFHLR17:"\<not>valid_attrconf noattrconf"
  assumes ATTRCONFHLR18:"attr_elem attr\<noteq>noelem\<and>
                        conf=noattrconf\<Longrightarrow>
                        valid_attrconf(attr_conf conf attr)"
  assumes ATTRCONFHLR19:"valid_attrconf conf\<and>
                        (\<not>find_elem conf attr)\<and>
                        attr_elem attr\<noteq>noelem\<Longrightarrow>
                        valid_attrconf(attr_conf conf attr)"
  assumes ATTRCONFHLR20:"attr_elem attr=noelem\<Longrightarrow>\<not>valid_attrconf(attr_conf conf attr)"
  assumes ATTRCONFHLR21:"conf\<noteq>noattrconf\<and>
                        \<not>valid_attrconf conf\<Longrightarrow>
                        \<not>valid_attrconf(attr_conf conf attr)"
  assumes ATTRCONFHLR22:"conf\<noteq>noattrconf\<and>
                         find_elem conf attr\<Longrightarrow>
                         \<not>valid_attrconf(attr_conf conf attr)"
  assumes ATTRCONFINDUCT:"\<lbrakk>P noattrconf;\<And>conf1 attr1. P conf1\<Longrightarrow>P(attr_conf conf1 attr1)\<rbrakk>\<Longrightarrow>P conf"
begin

lemma find_total:"find_elem conf attr\<or>
                   attr_elem attrx=attr_elem attr\<Longrightarrow>find_elem(attr_conf conf attrx) attr"
proof (erule disjE)
  assume "find_elem conf attr"
  from this show "find_elem (attr_conf conf attrx) attr" by (rule ATTRCONFHLR8)
next
  assume "attr_elem attrx = attr_elem attr"
  from this show "find_elem (attr_conf conf attrx) attr" by (rule ATTRCONFHLR7)
qed

lemma find_dual:
  "find_elem conf attr\<or>
   attr_elem attrx=attr_elem attr=
   (\<not>((\<not>find_elem conf attr)\<and>attr_elem attrx\<noteq>attr_elem attr))"
  by blast

lemma find_inverse:
  "find_elem(attr_conf conf attrx) attr\<Longrightarrow>find_elem conf attr\<or>
                                          attr_elem attrx=attr_elem attr"
proof -
  assume "find_elem(attr_conf conf attrx) attr"
  from this show "find_elem conf attr\<or>
                  attr_elem attrx=attr_elem attr"
  proof (rule contrapos_pp)
    assume "\<not> (find_elem conf attr \<or> attr_elem attrx = attr_elem attr)"
    from this have "(\<not>find_elem conf attr)\<and>attr_elem attrx\<noteq>attr_elem attr"
      by (auto simp:find_dual)
    from this show "\<not> find_elem (attr_conf conf attrx) attr"
      by (auto simp:ATTRCONFHLR9)
  qed
qed

lemma not_find_inverse:
  "\<not>find_elem(attr_conf conf attrx) attr\<Longrightarrow>(\<not>find_elem conf attr)\<and>
                                           attr_elem attrx\<noteq>attr_elem attr"
proof -
  assume "\<not>find_elem(attr_conf conf attrx) attr"
  from this show "(\<not>find_elem conf attr)\<and>
                 attr_elem attrx\<noteq>attr_elem attr"
  proof (rule contrapos_pp)
    assume "\<not> (\<not> find_elem conf attr \<and> attr_elem attrx \<noteq> attr_elem attr)"
    from this have "find_elem conf attr\<or>
                    attr_elem attrx=attr_elem attr" by auto
    from this show "\<not> \<not> find_elem (attr_conf conf attrx) attr"
      by (auto simp:find_total)
  qed
qed

lemma valid_total:"(attr_elem attr\<noteq>noelem\<and>
                    conf=noattrconf)\<or>
                    (valid_attrconf conf\<and>
                     (\<not>find_elem conf attr)\<and>
                     attr_elem attr\<noteq>noelem)\<Longrightarrow>valid_attrconf(attr_conf conf attr)"
proof (erule disjE)
  assume "attr_elem attr \<noteq> noelem \<and> conf = noattrconf"
  from this show "valid_attrconf (attr_conf conf attr)" by (rule ATTRCONFHLR18)
next
  assume "valid_attrconf conf \<and>
         \<not> find_elem conf attr \<and> attr_elem attr \<noteq> noelem"
  from this show "valid_attrconf (attr_conf conf attr)" by (rule ATTRCONFHLR19)
qed

lemma not_valid_total:"attr_elem attr=noelem\<or>
                       ((\<not>valid_attrconf conf)\<and>
                        conf\<noteq>noattrconf)\<or>
                       (conf\<noteq>noattrconf\<and>
                        find_elem conf attr)\<Longrightarrow>\<not>valid_attrconf(attr_conf conf attr)"
proof (erule disjE)
  assume "attr_elem attr = noelem"
  from this show "\<not>valid_attrconf(attr_conf conf attr)" by (rule ATTRCONFHLR20)
next
  show "\<not> valid_attrconf conf \<and> 
        conf \<noteq> noattrconf \<or>
        conf \<noteq> noattrconf \<and> 
        find_elem conf attr \<Longrightarrow>
        \<not> valid_attrconf (attr_conf conf attr)"
  proof (erule disjE)
    assume "\<not> valid_attrconf conf \<and> conf \<noteq> noattrconf"
    from this show "\<not> valid_attrconf (attr_conf conf attr)" by (auto simp: ATTRCONFHLR21)
  next
    assume "conf \<noteq> noattrconf \<and> find_elem conf attr"
    from this show "\<not> valid_attrconf (attr_conf conf attr)" by (auto simp: ATTRCONFHLR22)
  qed
qed

lemma valid_dual:
  "(attr_elem attr\<noteq>noelem\<and>conf=noattrconf)\<or>
   (valid_attrconf conf\<and>(\<not>find_elem conf attr)\<and>attr_elem attr\<noteq>noelem)=
   (\<not>(attr_elem attr=noelem\<or>
    ((\<not>valid_attrconf conf)\<and>conf\<noteq>noattrconf)\<or>
    (conf\<noteq>noattrconf\<and>find_elem conf attr)))"
  by blast

lemma valid_inverse:
  "valid_attrconf(attr_conf conf attr)\<Longrightarrow>(attr_elem attr\<noteq>noelem\<and>
                                         conf=noattrconf)\<or>
                                         (valid_attrconf conf\<and>
                                         (\<not>find_elem conf attr)\<and>
                                         attr_elem attr\<noteq>noelem)"
proof -
  assume "valid_attrconf(attr_conf conf attr)"
  from this show "(attr_elem attr\<noteq>noelem\<and>
                  conf=noattrconf)\<or>
                  (valid_attrconf conf\<and>
                  (\<not>find_elem conf attr)\<and>
                  attr_elem attr\<noteq>noelem)"
  proof (rule contrapos_pp)
    assume "\<not> (attr_elem attr \<noteq> noelem \<and> conf = noattrconf \<or>
            valid_attrconf conf \<and>
            \<not> find_elem conf attr \<and> attr_elem attr \<noteq> noelem)"
    from this have "attr_elem attr=noelem\<or>
                    ((\<not>valid_attrconf conf)\<and>conf\<noteq>noattrconf)\<or>
                    (conf\<noteq>noattrconf\<and>find_elem conf attr)"
      by (auto simp:valid_dual)
    from this show "\<not> valid_attrconf (attr_conf conf attr)"
      by (auto simp:not_valid_total)
  qed
qed

lemma not_valid_inverse:
  "\<not>valid_attrconf(attr_conf conf attr)\<Longrightarrow>attr_elem attr=noelem\<or>
                                          ((\<not>valid_attrconf conf)\<and>
                                          conf\<noteq>noattrconf)\<or>
                                          (conf\<noteq>noattrconf\<and>
                                          find_elem conf attr)"
proof -
  assume "\<not>valid_attrconf(attr_conf conf attr)"
  from this show "attr_elem attr=noelem\<or>
                  ((\<not>valid_attrconf conf)\<and>
                  conf\<noteq>noattrconf)\<or>
                  (conf\<noteq>noattrconf\<and>
                  find_elem conf attr)"
  proof (rule contrapos_pp)
    assume "\<not> (attr_elem attr = noelem \<or>
            \<not> valid_attrconf conf \<and> conf \<noteq> noattrconf \<or>
            conf \<noteq> noattrconf \<and> find_elem conf attr)"
    from this have "(attr_elem attr\<noteq>noelem\<and>conf=noattrconf)\<or>
                   (valid_attrconf conf\<and>(\<not>find_elem conf attr)\<and>attr_elem attr\<noteq>noelem)"
      by auto
    from this show "\<not> \<not> valid_attrconf (attr_conf conf attr)"
      by (auto simp:valid_total)
  qed
qed

lemma ATTRCONFHLR23:"noattrconf\<noteq>attr_conf conf attr"
proof
  fix conf attr
  assume 0:"noattrconf=attr_conf conf attr"
  from ATTRCONFHLR1 have "\<not>is_attrconf(attr_conf conf attr)" by(auto simp: 0)
  from this show "False" by (auto simp: ATTRCONFHLR2)
qed

lemma ATTRCONFHLR24:"x\<noteq>noattrconf\<Longrightarrow>\<exists>conf attr. x=attr_conf conf attr"
proof -
  fix x
  assume 0:"x\<noteq>noattrconf"
  from ATTRCONFHLR3 0 show "\<exists>sconf oconf. x = attr_conf sconf oconf" by blast 
qed

lemma ATTRCONFHLR25:"valid_attrconf conf\<and>
                     find_elem conf attr\<Longrightarrow>attr_elem attr\<noteq>noelem"
proof (induction rule:ATTRCONFINDUCT)
  show "valid_attrconf noattrconf \<and> find_elem noattrconf attr \<Longrightarrow>
        attr_elem attr \<noteq> noelem" by (auto simp:ATTRCONFHLR17)
next
  fix conf1 attr1
  show "(valid_attrconf conf1 \<and> find_elem conf1 attr \<Longrightarrow>
        attr_elem attr \<noteq> noelem) \<Longrightarrow>
        valid_attrconf (attr_conf conf1 attr1) \<and>
        find_elem (attr_conf conf1 attr1) attr \<Longrightarrow>
        attr_elem attr \<noteq> noelem"
  proof (auto)
    assume 1:"valid_attrconf conf1 \<and> find_elem conf1 attr \<Longrightarrow> False"
    assume 2:"find_elem (attr_conf conf1 attr1) attr"
    assume 3:"noelem = attr_elem attr"
    assume "valid_attrconf (attr_conf conf1 attr1)"
    from this have 4:"(attr_elem attr1\<noteq>noelem\<and>
                      conf1=noattrconf)\<or>
                      (valid_attrconf conf1\<and>
                      (\<not>find_elem conf1 attr1)\<and>
                      attr_elem attr1\<noteq>noelem)" by (auto simp:valid_inverse)
    from 2 have 2:"find_elem conf1 attr\<or>
                       attr_elem attr1=attr_elem attr" by (auto simp:find_inverse)
    from 2 3 4 have "(find_elem conf1 attr \<or> 
                     attr_elem attr1 = attr_elem attr)\<and>
                     (noelem = attr_elem attr)\<and>
                     (attr_elem attr1 \<noteq> noelem \<and> 
                     conf1 = noattrconf \<or>
                     valid_attrconf conf1 \<and>
                     \<not> find_elem conf1 attr1 \<and> 
                     attr_elem attr1 \<noteq> noelem)" by auto
    from this show False
    proof (auto simp:ATTRCONFHLR6)
      from 1 show "noelem = attr_elem attr \<Longrightarrow>
                  find_elem conf1 attr \<Longrightarrow>
                  valid_attrconf conf1 \<Longrightarrow>
                  \<not> find_elem conf1 attr1 \<Longrightarrow>
                  attr_elem attr1 \<noteq> attr_elem attr \<Longrightarrow> False" by (auto simp:1)
    qed
  qed
qed

lemma ATTRCONFHLR26:"find_elem conf attr\<and>
                    attr_elem attr=attr_elem attrx\<Longrightarrow>find_elem conf attrx"
proof (induction conf rule:ATTRCONFINDUCT)
  assume "find_elem noattrconf attr \<and> attr_elem attr = attr_elem attrx"
  from this show "find_elem noattrconf attrx" by (auto simp:ATTRCONFHLR6)
next
  fix conf1 attr1
  assume 0:"find_elem conf1 attr \<and> 
            attr_elem attr = attr_elem attrx \<Longrightarrow>
            find_elem conf1 attrx"
  assume "find_elem (attr_conf conf1 attr1) attr \<and>
          attr_elem attr = attr_elem attrx"
  from this have 1:"attr_elem attr = attr_elem attrx"
                 and 2:"find_elem (attr_conf conf1 attr1) attr" by auto
  from 2 have 2:"find_elem conf1 attr\<or>
                 attr_elem attr1=attr_elem attr" by (auto simp:find_inverse)
  from 1 2 show "find_elem (attr_conf conf1 attr1) attrx"
    by (auto simp add:0 ATTRCONFHLR8 ATTRCONFHLR7)
qed

lemma ATTRCONFHLR27:"find_elem conf attr\<and>
                    \<not>find_elem conf attrx\<Longrightarrow>attr_elem attr\<noteq>attr_elem attrx"
proof
  show "find_elem conf attr \<and> \<not> find_elem conf attrx \<Longrightarrow>
       attr_elem attr = attr_elem attrx \<Longrightarrow> False"
    by (auto simp:ATTRCONFHLR26)
qed

lemma ATTRCONFHLR28:"valid_attrconf conf\<and>
                     find_elem conf attr\<and>
                     attr_elem attr=elem\<Longrightarrow>attr_elem(get_attr conf elem)=elem"
proof (induction conf rule:ATTRCONFINDUCT)
  show "valid_attrconf noattrconf \<and>
       find_elem noattrconf attr \<and> attr_elem attr = elem \<Longrightarrow>
       attr_elem (get_attr noattrconf elem) = elem" by (auto simp:ATTRCONFHLR17)
next
  fix conf1 attr1
  assume 0:"valid_attrconf conf1 \<and>
           find_elem conf1 attr \<and> attr_elem attr = elem \<Longrightarrow>
           attr_elem (get_attr conf1 elem) = elem"
  assume "valid_attrconf (attr_conf conf1 attr1) \<and>
         find_elem (attr_conf conf1 attr1) attr \<and> attr_elem attr = elem"
  from this have 1:"valid_attrconf (attr_conf conf1 attr1)"
                 and 2:"find_elem (attr_conf conf1 attr1) attr"
                 and 3:"attr_elem attr = elem" by auto
  from 1 have 1:"(attr_elem attr1\<noteq>noelem\<and>
                 conf1=noattrconf)\<or>
                 (valid_attrconf conf1\<and>
                 (\<not>find_elem conf1 attr1)\<and>
                 attr_elem attr1\<noteq>noelem)" by (auto simp:valid_inverse)
  from 2 have 2:"find_elem conf1 attr\<or>
                 attr_elem attr1=attr_elem attr" by (auto simp:find_inverse)
  from 1 2 3 show "attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem"
  proof -
    show "attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf \<or>
          valid_attrconf conf1 \<and>
          \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem \<Longrightarrow>
          find_elem conf1 attr \<or> attr_elem attr1 = attr_elem attr \<Longrightarrow>
          attr_elem attr = elem \<Longrightarrow>
          attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem"
    proof (erule disjE)+
      show "attr_elem attr = elem \<Longrightarrow>
            attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf \<Longrightarrow>
            find_elem conf1 attr \<Longrightarrow>
            attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem" 
        by (auto simp:ATTRCONFHLR6)
    next
      show "attr_elem attr = elem \<Longrightarrow>
            attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf \<Longrightarrow>
            attr_elem attr1 = attr_elem attr \<Longrightarrow>
            attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem"
        by (auto simp:ATTRCONFHLR14)
    next
      show "find_elem conf1 attr \<or> attr_elem attr1 = attr_elem attr \<Longrightarrow>
            attr_elem attr = elem \<Longrightarrow>
            valid_attrconf conf1 \<and>
            \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem \<Longrightarrow>
            attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem"
      proof (erule disjE)
        show "attr_elem attr = elem \<Longrightarrow>
              valid_attrconf conf1 \<and>
              \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem \<Longrightarrow>
              attr_elem attr1 = attr_elem attr \<Longrightarrow>
              attr_elem (get_attr (attr_conf conf1 attr1) elem) = elem"
          by (auto simp:ATTRCONFHLR14)
      next
        assume 1:"attr_elem attr = elem"
        assume "valid_attrconf conf1 \<and>
                \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem"
        from this have 2:"valid_attrconf conf1"
                       and 3:"\<not> find_elem conf1 attr1"
                       and 4:"attr_elem attr1 \<noteq> noelem" by auto
        assume 5:"find_elem conf1 attr"
        from 5 3 1 have 6:"elem\<noteq>attr_elem attr1" 
          by (auto simp:ATTRCONFHLR27)
        from this have 6:"get_attr(attr_conf conf1 attr1) elem=get_attr conf1 elem"
          by (auto simp:ATTRCONFHLR16)
        show ?thesis
        proof (simp add:6)
          from 2 5 1 show "attr_elem (get_attr conf1 elem) = elem" by (auto simp:0)
        qed
      qed
    qed
  qed
qed

lemma ATTRCONFHLR29:"\<not>find_elem conf attr\<Longrightarrow>\<not>find_elem (delete_attr conf attr) attr"
proof (induction conf rule:ATTRCONFINDUCT)
  show "\<not> find_elem noattrconf attr \<Longrightarrow>
        \<not> find_elem (delete_attr noattrconf attr) attr"
    by (auto simp add:ATTRCONFHLR10)
next
  fix conf1 attr1
  assume 0:"\<not> find_elem conf1 attr \<Longrightarrow>
            \<not> find_elem (delete_attr conf1 attr) attr"
  assume 1:"\<not> find_elem (attr_conf conf1 attr1) attr"
  from this have 1:"(\<not>find_elem conf1 attr)\<and>
                    attr_elem attr1\<noteq>attr_elem attr" by (auto simp:not_find_inverse)
  from this have 1:"\<not>find_elem conf1 attr"
                 and 2:"attr_elem attr1\<noteq>attr_elem attr" by auto
  from 2 have 3:"delete_attr(attr_conf conf1 attr1) attr=
                 attr_conf (delete_attr conf1 attr) attr1" by (auto simp:ATTRCONFHLR12)
  show "\<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
  proof (simp add:3;rule ATTRCONFHLR9)
    from 1 2 show "\<not> find_elem (delete_attr conf1 attr) attr \<and>
                  attr_elem attr1 \<noteq> attr_elem attr" by (auto simp:0)
  qed
qed

lemma ATTRCONFHLR30:"\<not>find_elem conf attr\<and>
                    attr_elem attr=attr_elem attrx\<Longrightarrow>\<not>find_elem conf attrx"
proof
  assume "\<not> find_elem conf attr \<and> attr_elem attr = attr_elem attrx"
  from this have 0:"\<not> find_elem conf attr"
                 and 1:"attr_elem attr = attr_elem attrx" by auto
  assume "find_elem conf attrx"
  from this 1 have "find_elem conf attr" by (auto simp:ATTRCONFHLR26)
  from this 0 show False by auto
qed

lemma ATTRCONFHLR31:"valid_attrconf conf\<and>
                    find_elem conf attr\<Longrightarrow>\<not>find_elem(delete_attr conf attr) attr"
proof (induction conf rule:ATTRCONFINDUCT)
  show "valid_attrconf noattrconf \<and> find_elem noattrconf attr \<Longrightarrow>
        \<not> find_elem (delete_attr noattrconf attr) attr"
    by (auto simp:ATTRCONFHLR17)
next
  fix conf1
  fix attr1
  assume 0:"valid_attrconf conf1 \<and> find_elem conf1 attr \<Longrightarrow>
            \<not> find_elem (delete_attr conf1 attr) attr"
  assume "valid_attrconf (attr_conf conf1 attr1) \<and>
          find_elem (attr_conf conf1 attr1) attr"
  from this have 1:"valid_attrconf (attr_conf conf1 attr1)"
                 and 2:"find_elem (attr_conf conf1 attr1) attr" by auto
  from 1 have 1:"(attr_elem attr1\<noteq>noelem\<and>
                 conf1=noattrconf)\<or>
                 (valid_attrconf conf1\<and>
                 (\<not>find_elem conf1 attr1)\<and>
                 attr_elem attr1\<noteq>noelem)" by (auto simp:valid_inverse)
  from 2 have 2:"find_elem conf1 attr\<or>
                 attr_elem attr1=attr_elem attr" by (auto simp:find_inverse)
  from 1 2 show "\<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
  proof -
    show "attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf \<or>
          valid_attrconf conf1 \<and>
          \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem \<Longrightarrow>
          find_elem conf1 attr \<or> attr_elem attr1 = attr_elem attr \<Longrightarrow>
          \<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
    proof (erule disjE)+
      show "attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf \<Longrightarrow>
            find_elem conf1 attr \<Longrightarrow>
            \<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
        by (auto simp:ATTRCONFHLR6)
    next
      assume "attr_elem attr1 \<noteq> noelem \<and> conf1 = noattrconf"
      from this have 1:"conf1 = noattrconf" by auto
      assume "attr_elem attr1 = attr_elem attr"
      from this have 2:"delete_attr(attr_conf conf1 attr1) attr=delete_attr conf1 attr"
        by (auto simp:ATTRCONFHLR11)
      show "\<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
      proof (auto simp:2)
        show "find_elem (delete_attr conf1 attr) attr \<Longrightarrow> False"
          by (auto simp add:1 ATTRCONFHLR10 ATTRCONFHLR6)
      qed
    next
      show "find_elem conf1 attr \<or> attr_elem attr1 = attr_elem attr \<Longrightarrow>
           valid_attrconf conf1 \<and>
           \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem \<Longrightarrow>
           \<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
      proof (erule disjE)+
        assume "valid_attrconf conf1 \<and>
                \<not> find_elem conf1 attr1 \<and> attr_elem attr1 \<noteq> noelem"
        from this have 1:"valid_attrconf conf1"
                       and 2:"\<not> find_elem conf1 attr1"
                       and 3:"attr_elem attr1 \<noteq> noelem" by auto
        assume 4:"find_elem conf1 attr"
        from 4 2 have 6:"attr_elem attr\<noteq>attr_elem attr1" by (auto simp:ATTRCONFHLR27)
        from this have 5:"delete_attr(attr_conf conf1 attr1) attr=
                          attr_conf (delete_attr conf1 attr) attr1" 
          by (auto simp:ATTRCONFHLR12)
        show "\<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
        proof (simp add:5;rule ATTRCONFHLR9)
          from 1 4 6 show "\<not> find_elem (delete_attr conf1 attr) attr \<and>
                          attr_elem attr1 \<noteq> attr_elem attr"
            by (auto simp:0)
        qed
      next
        assume "valid_attrconf conf1 \<and>
                \<not> find_elem conf1 attr1 \<and> 
                attr_elem attr1 \<noteq> noelem"
        from this have 1:"valid_attrconf conf1"
                       and 2:"\<not> find_elem conf1 attr1"
                       and 3:"attr_elem attr1 \<noteq> noelem" by auto
        assume 4:"attr_elem attr1 = attr_elem attr"
        from this have 5:"delete_attr(attr_conf conf1 attr1) attr=delete_attr conf1 attr"
          by (auto simp:ATTRCONFHLR11)
        show "\<not> find_elem (delete_attr (attr_conf conf1 attr1) attr) attr"
        proof (simp add:5;rule ATTRCONFHLR29)
          from 2 4 show "\<not> find_elem conf1 attr" by (auto simp:ATTRCONFHLR30)
        qed
      qed
    qed
  qed
qed

end

print_locale! AttrConf

locale AttrConfRel=AttrConf noelem noattr noattrconf attr_conf is_attrconf attr_elem
                            find_elem delete_attr get_attr valid_attrconf
  for noelem::'element 
    and noattr::'attr
    and noattrconf::"'attrconf"
    and attr_conf::"'attrconf\<Rightarrow>'attr\<Rightarrow>'attrconf"
    and is_attrconf::"'attrconf\<Rightarrow>bool"
    and attr_elem::"'attr\<Rightarrow>'element"
    and find_elem::"'attrconf\<Rightarrow>'attr\<Rightarrow>bool"
    and delete_attr::"'attrconf\<Rightarrow>'attr\<Rightarrow>'attrconf"
    and get_attr::"'attrconf\<Rightarrow>'element\<Rightarrow>'attr"
    and valid_attrconf::"'attrconf\<Rightarrow>bool" +
  fixes rel_subset::"'attrconf\<Rightarrow>'attrconf\<Rightarrow>bool"
  assumes ATTRCONFRELHLR1:"rel_subset confx noattrconf"
  assumes ATTRCONFRELHLR2:"conf=noattrconf\<and>
                          find_elem confx attr\<Longrightarrow>
                          rel_subset confx (attr_conf conf attr)"
  assumes ATTRCONFRELHLR3:"conf\<noteq>noattrconf\<and>
                          find_elem confx attr\<and>
                          rel_subset confx conf\<Longrightarrow>
                          rel_subset confx (attr_conf conf attr)"
  assumes ATTRCONFRELHLR4:"\<not>rel_subset confx conf\<Longrightarrow>
                          \<not>rel_subset confx (attr_conf conf attr)"
  assumes ATTRCONFRELHLR5:"rel_subset confx conf\<and>
                           \<not>find_elem confx attr\<Longrightarrow>
                           \<not>rel_subset confx (attr_conf conf attr)"
begin

lemma rel_subset_total:"(conf=noattrconf\<and>
                        find_elem confx attr)\<or>
                        (conf\<noteq>noattrconf\<and>
                         find_elem confx attr\<and>
                         rel_subset confx conf)\<Longrightarrow>rel_subset confx (attr_conf conf attr)"
proof (erule disjE)
  assume "conf = noattrconf \<and> find_elem confx attr"
  from this show "rel_subset confx (attr_conf conf attr)" by (rule ATTRCONFRELHLR2)
next
  assume "conf \<noteq> noattrconf \<and> find_elem confx attr \<and> rel_subset confx conf"
  from this show "rel_subset confx (attr_conf conf attr)" by (rule ATTRCONFRELHLR3)
qed

lemma not_rel_subset_total:"(\<not>rel_subset confx conf)\<or>
                           (rel_subset confx conf\<and>\<not>find_elem confx attr)\<Longrightarrow>
                           \<not>rel_subset confx (attr_conf conf attr)"
proof (erule disjE)
  assume "\<not> rel_subset confx conf"
  from this show "\<not> rel_subset confx (attr_conf conf attr)" by (rule ATTRCONFRELHLR4)
next
  assume "rel_subset confx conf \<and> \<not> find_elem confx attr"
  from this show "\<not> rel_subset confx (attr_conf conf attr)" by (rule ATTRCONFRELHLR5)
qed

lemma rel_subset_dual:
  "(conf=noattrconf\<and>find_elem confx attr)\<or>
   (conf\<noteq>noattrconf\<and>find_elem confx attr\<and>rel_subset confx conf)=
   (\<not>((\<not>rel_subset confx conf)\<or>(rel_subset confx conf\<and>\<not>find_elem confx attr)))"
  by blast

lemma ATTRCONFRELHLR6:"rel_subset confx conf\<and>find_elem conf attr\<Longrightarrow>find_elem confx attr"
proof (induction conf rule:ATTRCONFINDUCT)
  assume "rel_subset confx noattrconf \<and> find_elem noattrconf attr"
  from this show "find_elem confx attr" by (auto simp:ATTRCONFHLR6)
next
  fix conf1 attr1
  assume 0:"rel_subset confx conf1 \<and> find_elem conf1 attr \<Longrightarrow>
            find_elem confx attr"
  assume "rel_subset confx (attr_conf conf1 attr1) \<and>
          find_elem (attr_conf conf1 attr1) attr"
  from this have 1:"rel_subset confx (attr_conf conf1 attr1)" 
                 and 2:"find_elem (attr_conf conf1 attr1) attr" by auto
  from 1 have 1:"(conf1=noattrconf\<and>
                  find_elem confx attr1)\<or>
                  (conf1\<noteq>noattrconf\<and>
                  find_elem confx attr1\<and>
                  rel_subset confx conf1)"
  proof (rule contrapos_pp)
    assume "\<not> (conf1 = noattrconf \<and> find_elem confx attr1 \<or>
            conf1 \<noteq> noattrconf \<and>
            find_elem confx attr1 \<and> rel_subset confx conf1)"
    from this have "((\<not>rel_subset confx conf1)\<or>
                    (rel_subset confx conf1\<and>\<not>find_elem confx attr1))" 
      by (auto simp:rel_subset_dual)
    from this show "\<not> rel_subset confx (attr_conf conf1 attr1)" 
      by (auto simp:not_rel_subset_total)
  qed
  from 2 have 2:"find_elem conf1 attr\<or>
                       attr_elem attr1=attr_elem attr"
  proof (rule contrapos_pp)
    assume "\<not> (find_elem conf1 attr \<or>
            attr_elem attr1 = attr_elem attr)"
    from this have "((\<not>find_elem conf1 attr)\<and>
                   attr_elem attr1\<noteq>attr_elem attr)" by (auto simp:find_dual)
    from this show "\<not> find_elem (attr_conf conf1 attr1) attr" by (rule ATTRCONFHLR9)
  qed
  from 1 2 have "(conf1 = noattrconf \<and> 
                  find_elem confx attr1 \<or>
                  conf1 \<noteq> noattrconf \<and> 
                  find_elem confx attr1 \<and> 
                  rel_subset confx conf1)\<and>
                  (find_elem conf1 attr \<or> 
                   attr_elem attr1 = attr_elem attr)" by auto
  from this show ?thesis by (auto simp add:0 ATTRCONFHLR26 ATTRCONFHLR6)
qed

end

print_locale! AttrConfRel

locale AttrConfDisj = arg1:AttrConf noelem noattr_arg1 noattrconf_arg1 attr_conf_arg1 is_attrconf_arg1 
                                    attr_elem_arg1 find_elem_arg1 delete_attr_arg1 get_attr_arg1
                                    valid_attrconf_arg1 +
                      arg2:AttrConf noelem noattr_arg2 noattrconf_arg2 attr_conf_arg2 is_attrconf_arg2
                                    attr_elem_arg2 find_elem_arg2 delete_attr_arg2 get_attr_arg2 
                                    valid_attrconf_arg2
  for noelem::'element 
    and noattr_arg1::'attr1
    and noattrconf_arg1::"'attrconf1"
    and attr_conf_arg1::"'attrconf1\<Rightarrow>'attr1\<Rightarrow>'attrconf1"
    and is_attrconf_arg1::"'attrconf1\<Rightarrow>bool"
    and attr_elem_arg1::"'attr1\<Rightarrow>'element"
    and find_elem_arg1::"'attrconf1\<Rightarrow>'attr1\<Rightarrow>bool"
    and delete_attr_arg1::"'attrconf1\<Rightarrow>'attr1\<Rightarrow>'attrconf1"
    and get_attr_arg1::"'attrconf1\<Rightarrow>'element\<Rightarrow>'attr1"
    and valid_attrconf_arg1::"'attrconf1\<Rightarrow>bool" 
    and noattr_arg2::'attr2
    and noattrconf_arg2::"'attrconf2"
    and attr_conf_arg2::"'attrconf2\<Rightarrow>'attr2\<Rightarrow>'attrconf2"
    and is_attrconf_arg2::"'attrconf2\<Rightarrow>bool"
    and attr_elem_arg2::"'attr2\<Rightarrow>'element"
    and find_elem_arg2::"'attrconf2\<Rightarrow>'attr2\<Rightarrow>bool"
    and delete_attr_arg2::"'attrconf2\<Rightarrow>'attr2\<Rightarrow>'attrconf2"
    and get_attr_arg2::"'attrconf2\<Rightarrow>'element\<Rightarrow>'attr2"
    and valid_attrconf_arg2::"'attrconf2\<Rightarrow>bool"+
  fixes rel_disjoint::"'attrconf1\<Rightarrow>'attrconf2\<Rightarrow>bool"
  assumes ATTRCONFDISJHLR1:"rel_disjoint conf1 noattrconf_arg2"
  assumes ATTRCONFDISJHLR2:"get_attr_arg1 conf1 (attr_elem_arg2 attr2)=noattr_arg1\<and>
                           rel_disjoint conf1 conf2\<Longrightarrow>
                           rel_disjoint conf1 (attr_conf_arg2 conf2 attr2)"
  assumes ATTRCONFDISJHLR3:"get_attr_arg1 conf1 (attr_elem_arg2 attr2)\<noteq>noattr_arg1\<and>
                           rel_disjoint conf1 conf2\<Longrightarrow>
                           \<not>rel_disjoint conf1 (attr_conf_arg2 conf2 attr2)"
  assumes ATTRCONFDISJHLR4:"get_attr_arg1 conf1 (attr_elem_arg2 attr2)=noattr_arg1\<and>
                           \<not>rel_disjoint conf1 conf2\<Longrightarrow>
                           \<not>rel_disjoint conf1 (attr_conf_arg2 conf2 attr2)"

print_locale! AttrConfDisj

end
