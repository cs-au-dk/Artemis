</div>

<?php get_sidebar(); ?>

<div id="footer">
    <?php bloginfo('name'); ?> site is powered by 
    <a href="http://wordpress.org">WordPress</a>
    <br><a href="<?php bloginfo('rss2_url'); ?>">Entries (RSS)</a>
    and <a href="<?php bloginfo('comments_rss2_url'); ?>">Comments (RSS)</a>.
    <br> <?php  wp_register("", " <strong>|</strong> "); wp_loginout(); ?>
    <!-- <?php echo $wpdb->num_queries; ?> queries. <?php timer_stop(1); ?> seconds. -->
</div>

<?php wp_footer(); ?>
<script src="http://www.google-analytics.com/urchin.js" type="text/javascript">
</script>
<script type="text/javascript">
_uacct = "UA-336489-2";
urchinTracker();
</script>
</body>
</html>
